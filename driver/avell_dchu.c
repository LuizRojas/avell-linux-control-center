// SPDX-License-Identifier: GPL-2.0-or-later
/*
 * avell_dchu - Linux driver for the Clevo/Insyde "DCHU" ACPI interface
 * (ACPI\CLV0001, \_SB.DCHU) found on Avell (Clevo based) notebooks.
 *
 * Native port of the Windows "Control Center 3.0" stack
 * (AcpiBridge.sys + InsydeDCHU.dll + DCHUService.exe). Every
 * Windows-side call ends up as:
 *
 *   \_SB.DCHU._DSM(93f224e4-fbdc-4bbf-add6-db71bdc0afad, 0, <command>,
 *                  Buffer(256) { <payload> })
 *
 * which is exactly what this driver issues through acpi_evaluate_dsm().
 * See docs/PROTOCOLO.md for the reverse engineering notes.
 *
 * Exposes:
 *   - platform_profile (quiet / low-power / balanced / performance)
 *   - hwmon: fan RPM, fan duty, CPU/GPU temperature
 *   - LED class "avell::kbd_backlight" (white or RGB 3-zone keyboards)
 *   - battery charge_control_{start,end}_threshold (FlexiCharger)
 *   - sysfs: fan_mode, kbd_color, kbd_effect, info attributes
 *   - input device for Fn hotkeys
 *   - /dev/avell-dchu raw _DSM ioctl (CAP_SYS_ADMIN only)
 */

#define pr_fmt(fmt) KBUILD_MODNAME ": " fmt

#include <linux/acpi.h>
#include <linux/ctype.h>
#include <linux/devm-helpers.h>
#include <linux/hwmon.h>
#include <linux/input.h>
#include <linux/input/sparse-keymap.h>
#include <linux/leds.h>
#include <linux/miscdevice.h>
#include <linux/module.h>
#include <linux/mutex.h>
#include <linux/platform_device.h>
#include <linux/platform_profile.h>
#include <linux/power_supply.h>
#include <linux/random.h>
#include <linux/slab.h>
#include <linux/uaccess.h>
#include <linux/version.h>
#include <acpi/battery.h>

#include "avell_dchu_ioctl.h"

/* platform_profile was reworked in 6.14 (class devices + ops table) */
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 14, 0)
#define AVELL_PPROF_CLASS	1
#endif

#define DCHU_BUF_LEN		256

/* _DSM function indices (the "command" argument of InsydeDCHU.dll) */
#define CMD_GET_EVENT		0x01
#define CMD_EC_PACKAGE		0x04	/* SetDCHU_DataEx(4, ...) sub-protocol */
#define CMD_FAN_STATUS		0x0c	/* GetWMIPackage(12) */
#define CMD_SYS_INFO		0x0d	/* GetWMIPackage(13) */
#define CMD_FEATURES16		0x10
#define CMD_KBD_WHITE		0x27	/* 39: white backlight level */
#define CMD_KBD_WHITE_GET	0x3d	/* 61 */
#define CMD_FEATURES96		0x60
#define CMD_KBD_RGB		0x67	/* 103: RGB keyboard */
#define CMD_OPT			0x79	/* 121: (sub << 24) | value */
#define CMD_FEATURES122		0x7a

/* CMD_OPT sub commands */
#define OPT_FAN_MODE		0x01
#define OPT_KBD_BOOT_EFFECT	0x1d
#define OPT_PERF_PROFILE	0x19
#define OPT_ANTI_DUST		0x29

/* CMD_EC_PACKAGE sub commands (payload byte 0) */
#define ECP_FLEXI_GET		0x1e
#define ECP_FLEXI_SET		0x1f

/* Performance profile values (CC30 "power modes") */
#define PERF_QUIET		0
#define PERF_POWER_SAVING	1
#define PERF_PERFORMANCE	2
#define PERF_ENTERTAINMENT	3

/* WMI13 keyboard types (byte 15) */
#define KBD_NONE		0
#define KBD_WHITE		1
#define KBD_RGB			2
#define KBD_PERKEY		3

/* RGB keyboard opcodes (top byte of the 32-bit word sent to cmd 103) */
#define RGB_ZONE_BASE		0xf0	/* 0xf0..0xf2 left/mid/right */
#define RGB_BRIGHTNESS		0xf4
#define RGB_ONOFF		0xe0

static const guid_t dchu_guid =
	GUID_INIT(0x93f224e4, 0xfbdc, 0x4bbf,
		  0xad, 0xd6, 0xdb, 0x71, 0xbd, 0xc0, 0xaf, 0xad);

static bool hotkey_kbd_control = true;
module_param(hotkey_kbd_control, bool, 0644);
MODULE_PARM_DESC(hotkey_kbd_control,
		 "Handle keyboard backlight Fn keys in the driver (default: on)");

struct avell_dchu {
	struct device *dev;
	acpi_handle handle;
	struct mutex lock;		/* serialises _DSM calls */

	u8 sysinfo[DCHU_BUF_LEN];	/* cached WMI13 */
	u32 feat16, feat96, feat122;
	u8 kbd_type;
	u8 fan_count;

	/* keyboard state (the firmware has no getter for most of it) */
	struct led_classdev kbd_led;
	unsigned int kbd_max;
	u32 kbd_color;			/* 0xRRGGBB, applied to all zones */
	u8 kbd_effect;
	bool kbd_sw_fx;			/* single zone: effects rendered here */
	struct delayed_work fx_work;
	unsigned int fx_tick;
	u32 fx_last, fx_from, fx_to;

#ifdef AVELL_PPROF_CLASS
	struct device *pprof_dev;
#else
	struct platform_profile_handler pprof;
#endif
	bool pprof_registered;
	enum platform_profile_option profile;

	struct acpi_battery_hook battery_hook;
	bool battery_hook_registered;

	struct input_dev *input;
	struct miscdevice misc;
	u8 fan_mode;
};

/* only one CLV0001 device can exist */
static struct avell_dchu *avell_global;

/* ------------------------------------------------------------------ */
/* Core transport                                                       */
/* ------------------------------------------------------------------ */

static int dchu_call_locked(struct avell_dchu *a, u32 cmd,
			    const void *in, size_t in_len,
			    u8 *out, size_t out_len, size_t *ret_len,
			    u64 *ret_int)
{
	union acpi_object arg, pkg, *obj;
	u8 *buf;
	int ret = 0;

	buf = kzalloc(DCHU_BUF_LEN, GFP_KERNEL);
	if (!buf)
		return -ENOMEM;
	if (in && in_len)
		memcpy(buf, in, min_t(size_t, in_len, DCHU_BUF_LEN));

	/*
	 * AcpiBridge.sys passes Arg3 as ACPI_METHOD_ARGUMENT_PACKAGE_EX
	 * wrapping the 256 byte buffer, i.e. Package() { Buffer(256) }.
	 * The firmware reads it with DerefOf(Arg3[0]); a bare buffer would
	 * only deliver its first byte.
	 */
	arg.type = ACPI_TYPE_BUFFER;
	arg.buffer.length = DCHU_BUF_LEN;
	arg.buffer.pointer = buf;
	pkg.type = ACPI_TYPE_PACKAGE;
	pkg.package.count = 1;
	pkg.package.elements = &arg;

	obj = acpi_evaluate_dsm(a->handle, &dchu_guid, 0, cmd, &pkg);
	kfree(buf);
	if (!obj)
		return -EIO;

	if (ret_len)
		*ret_len = 0;

	switch (obj->type) {
	case ACPI_TYPE_INTEGER:
		if (ret_int)
			*ret_int = obj->integer.value;
		if (out && out_len) {
			u64 v = obj->integer.value;
			size_t n = min_t(size_t, out_len, sizeof(v));

			memset(out, 0, out_len);
			memcpy(out, &v, n);	/* x86: little endian */
			if (ret_len)
				*ret_len = n;
		}
		break;
	case ACPI_TYPE_BUFFER:
		if (out && out_len) {
			size_t n = min_t(size_t, out_len, obj->buffer.length);

			memset(out, 0, out_len);
			memcpy(out, obj->buffer.pointer, n);
			if (ret_len)
				*ret_len = n;
		}
		if (ret_int) {
			u64 v = 0;

			memcpy(&v, obj->buffer.pointer,
			       min_t(size_t, sizeof(v), obj->buffer.length));
			*ret_int = v;
		}
		break;
	default:
		dev_dbg(a->dev, "cmd 0x%02x: unexpected object type %d\n",
			cmd, obj->type);
		ret = -EPROTO;
	}

	ACPI_FREE(obj);
	return ret;
}

static int dchu_call(struct avell_dchu *a, u32 cmd, const void *in,
		     size_t in_len, u8 *out, size_t out_len, size_t *ret_len,
		     u64 *ret_int)
{
	int ret;

	mutex_lock(&a->lock);
	ret = dchu_call_locked(a, cmd, in, in_len, out, out_len, ret_len,
			       ret_int);
	mutex_unlock(&a->lock);
	return ret;
}

/* SetWMI(cmd, data): 4 byte little endian word */
static int dchu_set_u32(struct avell_dchu *a, u32 cmd, u32 data)
{
	__le32 v = cpu_to_le32(data);

	return dchu_call(a, cmd, &v, sizeof(v), NULL, 0, NULL, NULL);
}

/* SetWMI(cmd, sub, data): sub command in the most significant byte */
static int dchu_set_opt(struct avell_dchu *a, u8 sub, u32 value)
{
	return dchu_set_u32(a, CMD_OPT, ((u32)sub << 24) | (value & 0xffffff));
}

static int dchu_get_int(struct avell_dchu *a, u32 cmd, u32 *val)
{
	u64 v = 0;
	int ret = dchu_call(a, cmd, NULL, 0, NULL, 0, NULL, &v);

	if (!ret)
		*val = (u32)v;
	return ret;
}

static int dchu_get_buf(struct avell_dchu *a, u32 cmd, u8 *out)
{
	return dchu_call(a, cmd, NULL, 0, out, DCHU_BUF_LEN, NULL, NULL);
}

/* SetDCHU_DataEx(4, in, 256, out) */
static int dchu_ec_package(struct avell_dchu *a, const u8 *in, size_t in_len,
			   u8 *out)
{
	return dchu_call(a, CMD_EC_PACKAGE, in, in_len, out,
			 out ? DCHU_BUF_LEN : 0, NULL, NULL);
}

/* ------------------------------------------------------------------ */
/* Platform profile                                                     */
/* ------------------------------------------------------------------ */

static int perf_from_profile(enum platform_profile_option p)
{
	switch (p) {
	case PLATFORM_PROFILE_QUIET:
		return PERF_QUIET;
	case PLATFORM_PROFILE_LOW_POWER:
		return PERF_POWER_SAVING;
	case PLATFORM_PROFILE_BALANCED:
		return PERF_ENTERTAINMENT;
	case PLATFORM_PROFILE_PERFORMANCE:
		return PERF_PERFORMANCE;
	default:
		return -EOPNOTSUPP;
	}
}

static int avell_profile_apply(struct avell_dchu *a,
			       enum platform_profile_option profile)
{
	int perf = perf_from_profile(profile);
	int ret;

	if (perf < 0)
		return perf;

	ret = dchu_set_opt(a, OPT_PERF_PROFILE, perf);
	if (ret)
		return ret;
	a->profile = profile;
	return 0;
}

#ifdef AVELL_PPROF_CLASS

static int avell_profile_probe(void *drvdata, unsigned long *choices)
{
	set_bit(PLATFORM_PROFILE_QUIET, choices);
	set_bit(PLATFORM_PROFILE_LOW_POWER, choices);
	set_bit(PLATFORM_PROFILE_BALANCED, choices);
	set_bit(PLATFORM_PROFILE_PERFORMANCE, choices);
	return 0;
}

static int avell_profile_get(struct device *dev,
			     enum platform_profile_option *profile)
{
	struct avell_dchu *a = dev_get_drvdata(dev);

	*profile = a->profile;
	return 0;
}

static int avell_profile_set(struct device *dev,
			     enum platform_profile_option profile)
{
	return avell_profile_apply(dev_get_drvdata(dev), profile);
}

static const struct platform_profile_ops avell_profile_ops = {
	.probe = avell_profile_probe,
	.profile_get = avell_profile_get,
	.profile_set = avell_profile_set,
};

static int avell_profile_init(struct avell_dchu *a)
{
	/*
	 * The firmware offers no getter; CC30 defaults to "Entertainment"
	 * (balanced). Apply it so our state matches the hardware.
	 */
	a->profile = PLATFORM_PROFILE_BALANCED;
	dchu_set_opt(a, OPT_PERF_PROFILE, PERF_ENTERTAINMENT);

	a->pprof_dev = platform_profile_register(a->dev, "avell-dchu", a,
						 &avell_profile_ops);
	if (IS_ERR(a->pprof_dev)) {
		int ret = PTR_ERR(a->pprof_dev);

		dev_warn(a->dev, "platform_profile unavailable (%d)\n", ret);
		return ret;
	}
	a->pprof_registered = true;
	return 0;
}

static void avell_profile_notify(struct avell_dchu *a)
{
	platform_profile_notify(a->pprof_dev);
}

static void avell_profile_exit(struct avell_dchu *a)
{
	platform_profile_remove(a->pprof_dev);
}

#else /* !AVELL_PPROF_CLASS */

static int avell_profile_get(struct platform_profile_handler *pprof,
			     enum platform_profile_option *profile)
{
	struct avell_dchu *a = container_of(pprof, struct avell_dchu, pprof);

	*profile = a->profile;
	return 0;
}

static int avell_profile_set(struct platform_profile_handler *pprof,
			     enum platform_profile_option profile)
{
	return avell_profile_apply(container_of(pprof, struct avell_dchu, pprof),
				   profile);
}

static int avell_profile_init(struct avell_dchu *a)
{
	int ret;

	a->pprof.profile_get = avell_profile_get;
	a->pprof.profile_set = avell_profile_set;
	set_bit(PLATFORM_PROFILE_QUIET, a->pprof.choices);
	set_bit(PLATFORM_PROFILE_LOW_POWER, a->pprof.choices);
	set_bit(PLATFORM_PROFILE_BALANCED, a->pprof.choices);
	set_bit(PLATFORM_PROFILE_PERFORMANCE, a->pprof.choices);

	a->profile = PLATFORM_PROFILE_BALANCED;
	dchu_set_opt(a, OPT_PERF_PROFILE, PERF_ENTERTAINMENT);

	ret = platform_profile_register(&a->pprof);
	if (ret) {
		dev_warn(a->dev, "platform_profile unavailable (%d)\n", ret);
		return ret;
	}
	a->pprof_registered = true;
	return 0;
}

static void avell_profile_notify(struct avell_dchu *a)
{
	platform_profile_notify();
}

static void avell_profile_exit(struct avell_dchu *a)
{
	platform_profile_remove();
}

#endif /* AVELL_PPROF_CLASS */

/* ------------------------------------------------------------------ */
/* hwmon                                                                */
/* ------------------------------------------------------------------ */

/* Offsets inside WMI12 (FAN.cs Read_FanSpeed) */
static const struct {
	u8 rpm_hi, duty, temp;
	const char *label;
} fan_map[] = {
	{  2, 16, 18, "CPU" },
	{  4, 19, 21, "GPU" },
	{  6, 22, 24, "GPU2" },
	{ 36, 38, 40, "System" },
};

static int avell_read_fans(struct avell_dchu *a, u8 *buf)
{
	return dchu_get_buf(a, CMD_FAN_STATUS, buf);
}

static umode_t avell_hwmon_visible(const void *data,
				   enum hwmon_sensor_types type,
				   u32 attr, int channel)
{
	const struct avell_dchu *a = data;
	int n = clamp_t(int, a->fan_count, 1, 2);

	switch (type) {
	case hwmon_fan:
	case hwmon_pwm:
	case hwmon_temp:
		return channel < n ? 0444 : 0;
	default:
		return 0;
	}
}

static int avell_hwmon_read(struct device *dev, enum hwmon_sensor_types type,
			    u32 attr, int channel, long *val)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	u8 *buf;
	int ret;

	buf = kmalloc(DCHU_BUF_LEN, GFP_KERNEL);
	if (!buf)
		return -ENOMEM;
	ret = avell_read_fans(a, buf);
	if (ret)
		goto out;

	switch (type) {
	case hwmon_fan:
		*val = (buf[fan_map[channel].rpm_hi] << 8) |
			buf[fan_map[channel].rpm_hi + 1];
		break;
	case hwmon_pwm:
		*val = buf[fan_map[channel].duty];	/* already 0..255 */
		break;
	case hwmon_temp:
		*val = buf[fan_map[channel].temp] * 1000;
		break;
	default:
		ret = -EOPNOTSUPP;
	}
out:
	kfree(buf);
	return ret;
}

static int avell_hwmon_read_string(struct device *dev,
				   enum hwmon_sensor_types type, u32 attr,
				   int channel, const char **str)
{
	*str = fan_map[channel].label;
	return 0;
}

static const struct hwmon_channel_info *const avell_hwmon_info[] = {
	HWMON_CHANNEL_INFO(fan, HWMON_F_INPUT | HWMON_F_LABEL,
			   HWMON_F_INPUT | HWMON_F_LABEL),
	HWMON_CHANNEL_INFO(pwm, HWMON_PWM_INPUT, HWMON_PWM_INPUT),
	HWMON_CHANNEL_INFO(temp, HWMON_T_INPUT | HWMON_T_LABEL,
			   HWMON_T_INPUT | HWMON_T_LABEL),
	NULL
};

static const struct hwmon_ops avell_hwmon_ops = {
	.is_visible = avell_hwmon_visible,
	.read = avell_hwmon_read,
	.read_string = avell_hwmon_read_string,
};

static const struct hwmon_chip_info avell_hwmon_chip = {
	.ops = &avell_hwmon_ops,
	.info = avell_hwmon_info,
};

/* ------------------------------------------------------------------ */
/* Keyboard backlight                                                   */
/* ------------------------------------------------------------------ */

/* RGBKB.SetBrightnessValue: 4 levels map to 47/95/143/191 */
static const u8 rgb_levels[] = { 0, 47, 95, 143, 191 };

static int kbd_rgb_apply_color(struct avell_dchu *a, u32 rgb)
{
	u8 r = (rgb >> 16) & 0xff, g = (rgb >> 8) & 0xff, b = rgb & 0xff;
	/* firmware word layout: B << 16 | R << 8 | G (RGBKB.SetColor) */
	u32 word = ((u32)b << 16) | ((u32)r << 8) | g;
	int zone, ret;

	for (zone = 0; zone < 3; zone++) {
		ret = dchu_set_u32(a, CMD_KBD_RGB,
				   ((u32)(RGB_ZONE_BASE + zone) << 24) | word);
		if (ret)
			return ret;
	}
	return 0;
}

/*
 * Keyboard effects. 3-zone keyboards (type 2) animate in the EC using
 * the RGBKB.cs effect words. Single-zone keyboards (type 6/22) have no
 * firmware animations -- CC30 hides the effect panel for them -- so the
 * effects that make sense on one zone are rendered here by a timer.
 */
enum {
	FX_STATIC, FX_BREATHE, FX_CYCLE, FX_DANCE, FX_TEMPO, FX_FLASH,
	FX_WAVE, FX_RANDOM,
};

static const struct {
	const char *name;
	u32 word;
	bool sw;		/* available as software effect */
} kbd_effects[] = {
	[FX_STATIC]  = { "static",  0,          true },
	[FX_BREATHE] = { "breathe", 0x1002a000, true },
	[FX_CYCLE]   = { "cycle",   0x33010000, true },
	[FX_DANCE]   = { "dance",   0x80000000, false },
	[FX_TEMPO]   = { "tempo",   0x90000000, false },
	[FX_FLASH]   = { "flash",   0xa0000000, true },
	[FX_WAVE]    = { "wave",    0xb0000000, false },
	[FX_RANDOM]  = { "random",  0x70000000, true },
};

#define FX_TICK_MS	80

static bool kbd_effect_available(struct avell_dchu *a, int i)
{
	return a->kbd_sw_fx ? kbd_effects[i].sw : true;
}

static u32 rgb_scale(u32 c, unsigned int k)	/* k: 0..255 */
{
	return ((((c >> 16) & 0xff) * k / 255) << 16) |
	       ((((c >> 8) & 0xff) * k / 255) << 8) |
	       ((c & 0xff) * k / 255);
}

static u32 rgb_lerp(u32 from, u32 to, unsigned int k, unsigned int n)
{
	u32 out = 0;
	int s;

	for (s = 0; s <= 16; s += 8) {
		int f = (from >> s) & 0xff, t = (to >> s) & 0xff;

		out |= (u32)(f + (t - f) * (int)k / (int)n) << s;
	}
	return out;
}

static u32 hue_to_rgb(unsigned int h)		/* h: 0..359, full S/V */
{
	unsigned int f = (h % 60) * 255 / 60, q = 255 - f;

	switch (h / 60) {
	case 0:  return 0xff0000 | (f << 8);
	case 1:  return (q << 16) | 0x00ff00;
	case 2:  return 0x00ff00 | f;
	case 3:  return (q << 8) | 0x0000ff;
	case 4:  return (f << 16) | 0x0000ff;
	default: return 0xff0000 | q;
	}
}

static void kbd_fx_work(struct work_struct *work)
{
	struct avell_dchu *a = container_of(to_delayed_work(work),
					    struct avell_dchu, fx_work);
	unsigned int t = a->fx_tick++;
	u32 c = READ_ONCE(a->kbd_color), out;

	switch (READ_ONCE(a->kbd_effect)) {
	case FX_BREATHE: {		/* ~3 s period, never fully dark */
		unsigned int p = t % 38, lvl = p < 19 ? p : 37 - p;

		out = rgb_scale(c, 15 + lvl * 240 / 18);
		break;
	}
	case FX_CYCLE:			/* full rainbow in ~4.8 s */
		out = hue_to_rgb((t * 6) % 360);
		break;
	case FX_FLASH:			/* 400 ms on / 400 ms off */
		out = (t / 5) % 2 ? 0 : c;
		break;
	case FX_RANDOM:			/* new colour every 1.2 s, 0.5 s fade */
		if (t % 15 == 0) {
			a->fx_from = a->fx_last;
			a->fx_to = hue_to_rgb(get_random_u32_below(360));
		}
		out = t % 15 < 6 ? rgb_lerp(a->fx_from, a->fx_to, t % 15, 6)
				 : a->fx_to;
		break;
	default:
		return;			/* static or hardware effect: stop */
	}

	if (a->kbd_led.brightness && out != a->fx_last) {
		if (kbd_rgb_apply_color(a, out)) {
			dev_warn_ratelimited(a->dev, "keyboard effect stopped\n");
			return;
		}
		a->fx_last = out;
	}
	schedule_delayed_work(&a->fx_work, msecs_to_jiffies(FX_TICK_MS));
}

static int kbd_apply_effect(struct avell_dchu *a, int i)
{
	cancel_delayed_work_sync(&a->fx_work);
	WRITE_ONCE(a->kbd_effect, i);

	if (i == FX_STATIC)
		return kbd_rgb_apply_color(a, a->kbd_color);
	if (!a->kbd_sw_fx)
		return dchu_set_u32(a, CMD_KBD_RGB, kbd_effects[i].word);

	a->fx_tick = 0;
	a->fx_last = a->fx_to = a->kbd_color;
	schedule_delayed_work(&a->fx_work, 0);
	return 0;
}

static int kbd_set_level(struct avell_dchu *a, unsigned int level)
{
	level = min(level, a->kbd_max);

	switch (a->kbd_type) {
	case KBD_WHITE:
		return dchu_set_u32(a, CMD_KBD_WHITE, level);
	case KBD_RGB:
	case KBD_PERKEY:
		if (!level)
			return dchu_set_u32(a, CMD_KBD_RGB,
					    (u32)RGB_BRIGHTNESS << 24);
		return dchu_set_u32(a, CMD_KBD_RGB,
				    ((u32)RGB_BRIGHTNESS << 24) |
				    rgb_levels[level]);
	default:
		return -ENODEV;
	}
}

static int kbd_led_set(struct led_classdev *cdev, enum led_brightness value)
{
	struct avell_dchu *a = container_of(cdev, struct avell_dchu, kbd_led);

	return kbd_set_level(a, value);
}

static enum led_brightness kbd_led_get(struct led_classdev *cdev)
{
	struct avell_dchu *a = container_of(cdev, struct avell_dchu, kbd_led);
	u32 v;

	if (a->kbd_type == KBD_WHITE &&
	    !dchu_get_int(a, CMD_KBD_WHITE_GET, &v) && v <= a->kbd_max)
		return v;
	return cdev->brightness;
}

static void kbd_step(struct avell_dchu *a, int delta, bool cycle)
{
	int level = a->kbd_led.brightness;

	if (cycle)
		level = level >= (int)a->kbd_max ? 0 : level + 1;
	else
		level = clamp_t(int, level + delta, 0, a->kbd_max);

	if (!kbd_set_level(a, level))
		led_classdev_notify_brightness_hw_changed(&a->kbd_led, level);
	a->kbd_led.brightness = level;
}

static int kbd_init(struct avell_dchu *a)
{
	if (a->kbd_type == KBD_NONE)
		return 0;

	if (a->kbd_type == KBD_WHITE)
		a->kbd_max = (a->feat122 & BIT(14)) ? 5 : 4;
	else
		a->kbd_max = ARRAY_SIZE(rgb_levels) - 1;

	a->kbd_led.name = "avell::kbd_backlight";
	a->kbd_led.max_brightness = a->kbd_max;
	a->kbd_led.brightness_set_blocking = kbd_led_set;
	a->kbd_led.brightness_get = kbd_led_get;
	a->kbd_led.flags = LED_BRIGHT_HW_CHANGED | LED_CORE_SUSPENDRESUME;
	a->kbd_color = 0xffffff;

	if (a->kbd_type == KBD_WHITE) {
		/* keep whatever level the EC currently has */
		a->kbd_led.brightness = kbd_led_get(&a->kbd_led);
	} else {
		/* no getter for RGB: all zones on, white, mid brightness */
		a->kbd_led.brightness = a->kbd_max / 2;
		dchu_set_u32(a, CMD_KBD_RGB, ((u32)RGB_ONOFF << 24) |
			     BIT(12) | (7 << 16) | 7);
		kbd_rgb_apply_color(a, a->kbd_color);
		kbd_set_level(a, a->kbd_led.brightness);
	}

	return devm_led_classdev_register(a->dev, &a->kbd_led);
}

/* ------------------------------------------------------------------ */
/* FlexiCharger -> power_supply charge thresholds                       */
/* ------------------------------------------------------------------ */

static int flexi_get(struct avell_dchu *a, u8 *en, u8 *start, u8 *stop)
{
	u8 in[1] = { ECP_FLEXI_GET };
	u8 *out;
	int ret;

	out = kzalloc(DCHU_BUF_LEN, GFP_KERNEL);
	if (!out)
		return -ENOMEM;
	ret = dchu_ec_package(a, in, sizeof(in), out);
	if (!ret) {
		*en = out[0];
		*start = out[1];
		*stop = out[2];
	}
	kfree(out);
	return ret;
}

static int flexi_set(struct avell_dchu *a, u8 en, u8 start, u8 stop)
{
	u8 in[4] = { ECP_FLEXI_SET, en, start, stop };
	u8 *out;
	int ret;

	out = kzalloc(DCHU_BUF_LEN, GFP_KERNEL);
	if (!out)
		return -ENOMEM;
	ret = dchu_ec_package(a, in, sizeof(in), out);
	kfree(out);
	return ret;
}

static ssize_t charge_threshold_show(struct device *dev, char *buf, bool end)
{
	struct avell_dchu *a = avell_global;
	u8 en, start, stop;
	int ret;

	if (!a)
		return -ENODEV;
	ret = flexi_get(a, &en, &start, &stop);
	if (ret)
		return ret;
	if (!en)
		return sysfs_emit(buf, "%d\n", end ? 100 : 0);
	return sysfs_emit(buf, "%u\n", end ? stop : start);
}

static ssize_t charge_threshold_store(struct device *dev, const char *buf,
				      size_t count, bool end)
{
	struct avell_dchu *a = avell_global;
	u8 en, start, stop;
	unsigned int v;
	int ret;

	if (!a)
		return -ENODEV;
	ret = kstrtouint(buf, 10, &v);
	if (ret)
		return ret;
	if (v > 100)
		return -EINVAL;

	ret = flexi_get(a, &en, &start, &stop);
	if (ret)
		return ret;
	if (!en) {		/* firmware defaults used by CC30 */
		start = 70;
		stop = 100;
	}
	if (end)
		stop = v;
	else
		start = v;
	if (start >= stop) {
		if (end)
			start = stop > 10 ? stop - 10 : 0;
		else
			return -EINVAL;
	}

	en = !(stop >= 100 && start == 0);
	ret = flexi_set(a, en, start, stop);
	return ret ? ret : count;
}

static ssize_t charge_control_start_threshold_show(struct device *dev,
						   struct device_attribute *attr,
						   char *buf)
{
	return charge_threshold_show(dev, buf, false);
}

static ssize_t charge_control_start_threshold_store(struct device *dev,
						    struct device_attribute *attr,
						    const char *buf, size_t count)
{
	return charge_threshold_store(dev, buf, count, false);
}

static ssize_t charge_control_end_threshold_show(struct device *dev,
						 struct device_attribute *attr,
						 char *buf)
{
	return charge_threshold_show(dev, buf, true);
}

static ssize_t charge_control_end_threshold_store(struct device *dev,
						  struct device_attribute *attr,
						  const char *buf, size_t count)
{
	return charge_threshold_store(dev, buf, count, true);
}

static DEVICE_ATTR_RW(charge_control_start_threshold);
static DEVICE_ATTR_RW(charge_control_end_threshold);

static struct attribute *avell_battery_attrs[] = {
	&dev_attr_charge_control_start_threshold.attr,
	&dev_attr_charge_control_end_threshold.attr,
	NULL
};
ATTRIBUTE_GROUPS(avell_battery);

static int avell_battery_add(struct power_supply *battery,
			     struct acpi_battery_hook *hook)
{
	return device_add_groups(&battery->dev, avell_battery_groups);
}

static int avell_battery_remove(struct power_supply *battery,
				struct acpi_battery_hook *hook)
{
	device_remove_groups(&battery->dev, avell_battery_groups);
	return 0;
}

static void avell_battery_init(struct avell_dchu *a)
{
	u8 en, start, stop;

	/* Only hook the battery if the EC answers the FlexiCharger query */
	if (flexi_get(a, &en, &start, &stop)) {
		dev_info(a->dev, "FlexiCharger not supported\n");
		return;
	}
	a->battery_hook.name = "Avell FlexiCharger";
	a->battery_hook.add_battery = avell_battery_add;
	a->battery_hook.remove_battery = avell_battery_remove;
	if (!devm_battery_hook_register(a->dev, &a->battery_hook))
		a->battery_hook_registered = true;
}

/* ------------------------------------------------------------------ */
/* Misc sysfs attributes on the platform device                         */
/* ------------------------------------------------------------------ */

static const struct {
	const char *name;
	u8 value;
} fan_modes[] = {
	{ "auto",   0 },
	{ "max",    1 },
	{ "maxq",   5 },
	{ "custom", 6 },
	{ "silent", 8 },
};

static ssize_t fan_mode_show(struct device *dev, struct device_attribute *attr,
			     char *buf)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	int i, len = 0;

	for (i = 0; i < ARRAY_SIZE(fan_modes); i++)
		len += sysfs_emit_at(buf, len,
				     fan_modes[i].value == a->fan_mode ?
				     "[%s] " : "%s ", fan_modes[i].name);
	buf[len - 1] = '\n';
	return len;
}

static ssize_t fan_mode_store(struct device *dev, struct device_attribute *attr,
			      const char *buf, size_t count)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	int i, ret;

	for (i = 0; i < ARRAY_SIZE(fan_modes); i++) {
		if (sysfs_streq(buf, fan_modes[i].name)) {
			ret = dchu_set_opt(a, OPT_FAN_MODE, fan_modes[i].value);
			if (ret)
				return ret;
			a->fan_mode = fan_modes[i].value;
			return count;
		}
	}
	return -EINVAL;
}
static DEVICE_ATTR_RW(fan_mode);

static ssize_t kbd_type_show(struct device *dev, struct device_attribute *attr,
			     char *buf)
{
	static const char * const names[] = {
		[KBD_NONE] = "none", [KBD_WHITE] = "white",
		[KBD_RGB] = "rgb", [KBD_PERKEY] = "perkey",
	};
	struct avell_dchu *a = dev_get_drvdata(dev);

	return sysfs_emit(buf, "%s\n", names[a->kbd_type]);
}
static DEVICE_ATTR_RO(kbd_type);

static ssize_t kbd_color_show(struct device *dev, struct device_attribute *attr,
			      char *buf)
{
	struct avell_dchu *a = dev_get_drvdata(dev);

	return sysfs_emit(buf, "%06x\n", a->kbd_color);
}

static ssize_t kbd_color_store(struct device *dev,
			       struct device_attribute *attr,
			       const char *buf, size_t count)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	u32 rgb;
	int ret;

	if (a->kbd_type == KBD_NONE || a->kbd_type == KBD_WHITE)
		return -EOPNOTSUPP;
	if (*buf == '#')
		buf++;
	ret = kstrtou32(buf, 16, &rgb);
	if (ret)
		return ret;
	if (rgb > 0xffffff)
		return -EINVAL;
	WRITE_ONCE(a->kbd_color, rgb);
	/* software breathe/flash follow the new colour; anything else goes static */
	if (a->kbd_sw_fx && (a->kbd_effect == FX_BREATHE ||
			     a->kbd_effect == FX_FLASH))
		return count;
	ret = kbd_apply_effect(a, FX_STATIC);
	return ret ? ret : count;
}
static DEVICE_ATTR_RW(kbd_color);

static ssize_t kbd_effect_show(struct device *dev,
			       struct device_attribute *attr, char *buf)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	int i, len = 0;

	for (i = 0; i < ARRAY_SIZE(kbd_effects); i++)
		if (kbd_effect_available(a, i))
			len += sysfs_emit_at(buf, len, i == a->kbd_effect ?
					     "[%s] " : "%s ",
					     kbd_effects[i].name);
	buf[len - 1] = '\n';
	return len;
}

static ssize_t kbd_effect_store(struct device *dev,
				struct device_attribute *attr,
				const char *buf, size_t count)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	int i, ret;

	if (a->kbd_type == KBD_NONE || a->kbd_type == KBD_WHITE)
		return -EOPNOTSUPP;

	for (i = 0; i < ARRAY_SIZE(kbd_effects); i++) {
		if (!sysfs_streq(buf, kbd_effects[i].name))
			continue;
		if (!kbd_effect_available(a, i))
			return -EOPNOTSUPP;
		ret = kbd_apply_effect(a, i);
		return ret ? ret : count;
	}
	return -EINVAL;
}
static DEVICE_ATTR_RW(kbd_effect);

static ssize_t anti_dust_store(struct device *dev,
			       struct device_attribute *attr,
			       const char *buf, size_t count)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	bool run;
	int ret;

	ret = kstrtobool(buf, &run);
	if (ret)
		return ret;
	if (!run)
		return count;
	ret = dchu_set_opt(a, OPT_ANTI_DUST, 1);
	return ret ? ret : count;
}
static DEVICE_ATTR_WO(anti_dust);

static ssize_t features_show(struct device *dev,
			     struct device_attribute *attr, char *buf)
{
	struct avell_dchu *a = dev_get_drvdata(dev);

	return sysfs_emit(buf, "wmi16=0x%08x wmi96=0x%08x wmi122=0x%08x fans=%u kbd=%u\n",
			  a->feat16, a->feat96, a->feat122, a->fan_count,
			  a->sysinfo[15]);
}
static DEVICE_ATTR_RO(features);

static ssize_t ec_version_show(struct device *dev,
			       struct device_attribute *attr, char *buf)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	char ver[32] = "1.";
	u8 in[7] = { 1, 0, 0, 0, 0, 0, 0xde };
	u8 *out;
	int i, j, pos = 2, ret = 0;

	out = kzalloc(DCHU_BUF_LEN, GFP_KERNEL);
	if (!out)
		return -ENOMEM;

	/* InsydeDriver.GetECVersion: 4 reads, 5 bytes each from out[1..5] */
	for (i = 0; i < 4 && !ret; i++) {
		in[1] = i;
		ret = dchu_ec_package(a, in, sizeof(in), out);
		if (i == 0)
			continue;
		for (j = 1; j <= 5 && pos < sizeof(ver) - 1; j++)
			ver[pos++] = out[j];
	}
	kfree(out);
	if (ret)
		return ret;
	ver[pos] = '\0';
	for (i = 0; ver[i]; i++)
		if (ver[i] == '$' || !isprint(ver[i])) {
			ver[i] = '\0';
			break;
		}
	/* some EC firmwares (e.g. A50i 1.07.01TBN) answer with zeros */
	if (strlen(ver) <= 2)
		return -ENODATA;
	return sysfs_emit(buf, "%s\n", ver);
}
static DEVICE_ATTR_RO(ec_version);

static struct attribute *avell_attrs[] = {
	&dev_attr_fan_mode.attr,
	&dev_attr_kbd_type.attr,
	&dev_attr_kbd_color.attr,
	&dev_attr_kbd_effect.attr,
	&dev_attr_anti_dust.attr,
	&dev_attr_features.attr,
	&dev_attr_ec_version.attr,
	NULL
};

static umode_t avell_attr_visible(struct kobject *kobj, struct attribute *attr,
				  int n)
{
	struct avell_dchu *a = dev_get_drvdata(kobj_to_dev(kobj));

	if ((attr == &dev_attr_kbd_color.attr ||
	     attr == &dev_attr_kbd_effect.attr) &&
	    (a->kbd_type == KBD_NONE || a->kbd_type == KBD_WHITE))
		return 0;
	return attr->mode;
}

static const struct attribute_group avell_group = {
	.attrs = avell_attrs,
	.is_visible = avell_attr_visible,
};

/* ------------------------------------------------------------------ */
/* Hotkeys                                                              */
/* ------------------------------------------------------------------ */

/* Event codes from FnKey.exe Form1.Arg001_GetEvent */
#define EV_KBD_DOWN		0x81
#define EV_KBD_UP		0x82
#define EV_KBD_CYCLE		0x8a
#define EV_KBD_TOGGLE		0x9f
#define EV_KBD_TOGGLE2		0x9e
#define EV_POWER_MODE		0x59

static const struct key_entry avell_keymap[] = {
	{ KE_KEY, 0x59, { KEY_PROG3 } },		/* Fn+3 power mode */
	{ KE_KEY, 0x85, { KEY_RFKILL } },		/* airplane */
	{ KE_KEY, 0x95, { KEY_PROG1 } },		/* Control Center */
	{ KE_KEY, 0xfc, { KEY_TOUCHPAD_TOGGLE } },
	{ KE_KEY, 0xfd, { KEY_TOUCHPAD_TOGGLE } },
	{ KE_KEY, 0x81, { KEY_KBDILLUMDOWN } },
	{ KE_KEY, 0x82, { KEY_KBDILLUMUP } },
	{ KE_KEY, 0x8a, { KEY_KBDILLUMTOGGLE } },
	{ KE_KEY, 0x9e, { KEY_KBDILLUMTOGGLE } },
	{ KE_KEY, 0x9f, { KEY_KBDILLUMTOGGLE } },
	{ KE_END, 0 }
};

static void avell_cycle_profile(struct avell_dchu *a)
{
	static const enum platform_profile_option order[] = {
		PLATFORM_PROFILE_QUIET, PLATFORM_PROFILE_LOW_POWER,
		PLATFORM_PROFILE_PERFORMANCE, PLATFORM_PROFILE_BALANCED,
	};
	int i, cur = 0;

	if (!a->pprof_registered)
		return;
	for (i = 0; i < ARRAY_SIZE(order); i++)
		if (order[i] == a->profile)
			cur = i;
	if (!avell_profile_apply(a, order[(cur + 1) % ARRAY_SIZE(order)]))
		avell_profile_notify(a);
}

static void avell_handle_event(struct avell_dchu *a, u32 code)
{
	bool kbd_handled = false;

	code &= 0xff;
	dev_dbg(a->dev, "hotkey event 0x%02x\n", code);

	if (hotkey_kbd_control && a->kbd_type != KBD_NONE) {
		kbd_handled = true;
		switch (code) {
		case EV_KBD_DOWN:
			kbd_step(a, -1, false);
			break;
		case EV_KBD_UP:
			kbd_step(a, 1, false);
			break;
		case EV_KBD_CYCLE:
			kbd_step(a, 0, true);
			break;
		case EV_KBD_TOGGLE:
		case EV_KBD_TOGGLE2:
			kbd_step(a, a->kbd_led.brightness ?
				 -(int)a->kbd_max : (int)a->kbd_max / 2, false);
			break;
		default:
			kbd_handled = false;
		}
	}
	if (kbd_handled)
		return;

	if (code == EV_POWER_MODE)
		avell_cycle_profile(a);

	if (a->input)
		sparse_keymap_report_event(a->input, code, 1, true);
}

static void avell_notify(acpi_handle handle, u32 event, void *data)
{
	struct avell_dchu *a = data;
	u32 code = 0;

	/*
	 * The Windows bridge forwards the notify value; Clevo firmware
	 * additionally queues the real event behind _DSM function 1.
	 * Prefer the queued event and fall back to the notify value.
	 */
	if (dchu_get_int(a, CMD_GET_EVENT, &code) || !code || code == 0xffffffff)
		code = event;
	avell_handle_event(a, code);
}

static int avell_input_init(struct avell_dchu *a)
{
	int ret;

	a->input = devm_input_allocate_device(a->dev);
	if (!a->input)
		return -ENOMEM;
	a->input->name = "Avell DCHU Hotkeys";
	a->input->phys = "avell-dchu/input0";
	a->input->id.bustype = BUS_HOST;
	ret = sparse_keymap_setup(a->input, avell_keymap, NULL);
	if (ret)
		return ret;
	return input_register_device(a->input);
}

/* ------------------------------------------------------------------ */
/* /dev/avell-dchu raw interface                                        */
/* ------------------------------------------------------------------ */

static long avell_misc_ioctl(struct file *f, unsigned int cmd,
			     unsigned long arg)
{
	struct avell_dchu *a = container_of(f->private_data,
					    struct avell_dchu, misc);
	struct avell_dchu_call *c;
	size_t ret_len = 0;
	u64 ret_int = 0;
	int ret;

	if (cmd != AVELL_DCHU_IOC_CALL)
		return -ENOTTY;
	if (!capable(CAP_SYS_ADMIN))
		return -EPERM;

	c = memdup_user((void __user *)arg, sizeof(*c));
	if (IS_ERR(c))
		return PTR_ERR(c);

	ret = dchu_call(a, c->command, c->in, sizeof(c->in), c->out,
			sizeof(c->out), &ret_len, &ret_int);
	if (!ret) {
		c->out_len = ret_len;
		c->out_int = ret_int;
		if (copy_to_user((void __user *)arg, c, sizeof(*c)))
			ret = -EFAULT;
	}
	kfree(c);
	return ret;
}

static const struct file_operations avell_misc_fops = {
	.owner = THIS_MODULE,
	.unlocked_ioctl = avell_misc_ioctl,
	.compat_ioctl = compat_ptr_ioctl,
};

/* ------------------------------------------------------------------ */
/* Probe                                                                */
/* ------------------------------------------------------------------ */

static void avell_read_features(struct avell_dchu *a)
{
	u8 t;

	if (dchu_get_buf(a, CMD_SYS_INFO, a->sysinfo))
		dev_warn(a->dev, "could not read WMI13 system info\n");
	dchu_get_int(a, CMD_FEATURES16, &a->feat16);
	dchu_get_int(a, CMD_FEATURES96, &a->feat96);
	dchu_get_int(a, CMD_FEATURES122, &a->feat122);

	a->fan_count = a->sysinfo[12];
	a->fan_mode = a->sysinfo[14] == 5 ? 5 : 0;

	t = a->sysinfo[15];
	if (t == 1)
		a->kbd_type = KBD_WHITE;
	else if (t == 2 || t == 6 || t == 22)
		a->kbd_type = KBD_RGB;
	else if (t == 3 || t == 19 || t == 35 || t == 51 || t == 243)
		a->kbd_type = KBD_PERKEY;
	else
		a->kbd_type = KBD_NONE;
	a->kbd_sw_fx = (t == 6 || t == 22);

	dev_info(a->dev, "fans=%u keyboard=%u wmi16=0x%x wmi96=0x%x wmi122=0x%x\n",
		 a->fan_count, t, a->feat16, a->feat96, a->feat122);
}

static int avell_probe(struct platform_device *pdev)
{
	struct avell_dchu *a;
	struct device *hwmon;
	acpi_status status;
	int ret;

	if (avell_global)
		return -EBUSY;

	a = devm_kzalloc(&pdev->dev, sizeof(*a), GFP_KERNEL);
	if (!a)
		return -ENOMEM;
	a->dev = &pdev->dev;
	a->handle = ACPI_HANDLE(&pdev->dev);
	if (!a->handle)
		return -ENODEV;
	mutex_init(&a->lock);
	platform_set_drvdata(pdev, a);
	ret = devm_delayed_work_autocancel(&pdev->dev, &a->fx_work, kbd_fx_work);
	if (ret)
		return ret;

	if (!acpi_check_dsm(a->handle, &dchu_guid, 0, BIT(CMD_SYS_INFO)) &&
	    !acpi_has_method(a->handle, "_DSM")) {
		dev_err(a->dev, "DCHU _DSM not present\n");
		return -ENODEV;
	}

	avell_read_features(a);

	ret = devm_device_add_group(a->dev, &avell_group);
	if (ret)
		return ret;

	hwmon = devm_hwmon_device_register_with_info(a->dev, "avell_dchu", a,
						     &avell_hwmon_chip, NULL);
	if (IS_ERR(hwmon))
		dev_warn(a->dev, "hwmon registration failed\n");

	ret = kbd_init(a);
	if (ret)
		dev_warn(a->dev, "keyboard backlight init failed (%d)\n", ret);

	avell_profile_init(a);

	ret = avell_input_init(a);
	if (ret)
		dev_warn(a->dev, "hotkey input init failed (%d)\n", ret);

	status = acpi_install_notify_handler(a->handle, ACPI_DEVICE_NOTIFY,
					     avell_notify, a);
	if (ACPI_FAILURE(status))
		dev_warn(a->dev, "cannot install notify handler\n");

	a->misc.minor = MISC_DYNAMIC_MINOR;
	a->misc.name = "avell-dchu";
	a->misc.fops = &avell_misc_fops;
	a->misc.mode = 0600;
	ret = misc_register(&a->misc);
	if (ret)
		dev_warn(a->dev, "misc device registration failed (%d)\n", ret);

	avell_global = a;
	avell_battery_init(a);

	dev_info(a->dev, "Avell DCHU interface ready\n");
	return 0;
}

static void avell_remove(struct platform_device *pdev)
{
	struct avell_dchu *a = platform_get_drvdata(pdev);

	acpi_remove_notify_handler(a->handle, ACPI_DEVICE_NOTIFY, avell_notify);
	if (a->misc.fops)
		misc_deregister(&a->misc);
	if (a->pprof_registered)
		avell_profile_exit(a);
	/* battery hook is devm managed; clear global after it is gone */
	avell_global = NULL;
}

static int avell_suspend(struct device *dev)
{
	struct avell_dchu *a = dev_get_drvdata(dev);

	if (a->kbd_type == KBD_RGB || a->kbd_type == KBD_PERKEY)
		cancel_delayed_work_sync(&a->fx_work);
	return 0;
}

static int avell_resume(struct device *dev)
{
	struct avell_dchu *a = dev_get_drvdata(dev);
	int perf = perf_from_profile(a->profile);

	if (perf >= 0)
		dchu_set_opt(a, OPT_PERF_PROFILE, perf);
	if (a->fan_mode)
		dchu_set_opt(a, OPT_FAN_MODE, a->fan_mode);
	if (a->kbd_type == KBD_RGB || a->kbd_type == KBD_PERKEY)
		kbd_apply_effect(a, a->kbd_effect);
	return 0;
}

static DEFINE_SIMPLE_DEV_PM_OPS(avell_pm, avell_suspend, avell_resume);

static const struct acpi_device_id avell_acpi_ids[] = {
	{ "CLV0001", 0 },
	{ }
};
MODULE_DEVICE_TABLE(acpi, avell_acpi_ids);

static struct platform_driver avell_driver = {
	.driver = {
		.name = "avell-dchu",
		.acpi_match_table = avell_acpi_ids,
		.pm = pm_sleep_ptr(&avell_pm),
	},
	.probe = avell_probe,
	.remove = avell_remove,
};
module_platform_driver(avell_driver);

MODULE_AUTHOR("Luiz Rojas");
MODULE_DESCRIPTION("Avell/Clevo DCHU ACPI interface (Control Center for Linux)");
MODULE_LICENSE("GPL");

"""
Pathao fare-quote logger
Android Studio emulator + Appium (UiAutomator2) + Python.
Calibrated against the Pathao user app (com.pathao.user) screens of Nov 2026.

It reads the "Ride Details" fare screen only and never books a ride: every tap
goes through safe_click(), which refuses "Choose ..."/request/booking controls
and stops the run.

Flow per route
  set emulator GPS to pickup -> open Pathao -> tap Car -> type destination ->
  tap the matching search result -> read every ride card (Bike, CNG, Car Plus,
  Car Prime, ...) -> screenshot -> Back.

Commands
  python pathao_fare_bot.py dump                 # print + save the current screen
  python pathao_fare_bot.py once --route R11     # quote one route
  python pathao_fare_bot.py run --slot offpeak   # quote every route once, now
  python pathao_fare_bot.py schedule             # run each slot in CONFIG["slots"] daily, Dhaka time

Output
  data/fares.csv        one row per route x ride type
  data/screens/*.png    a screenshot of every fare screen (and of every error)
"""

import argparse
import csv
import os
import random
import re
import subprocess
import time
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

from appium import webdriver
from appium.options.android import UiAutomator2Options
from appium.webdriver.common.appiumby import AppiumBy

# =============================================================== CONFIG
CONFIG = {
    "appium_url": "http://127.0.0.1:4723",
    "udid": "emulator-5554",            # from `adb devices`
    "avd_name": "pathao_bot",           # the AVD you created in Android Studio
    "headless": False,                  # True = start emulator with no window
    "app_package": "com.pathao.user",   # confirmed

    # Ride types to keep. Empty list = keep every card Pathao shows.
    "keep_types": [],                   # e.g. ["Car Plus", "Car Prime", "Car Max"]
    # Ride types never logged (no per-trip price).
    "skip_types": ["Rent a Car"],

    # Daily slots, Asia/Dhaka. A slot takes ~1.5-2 min per route.
    "slots": {"morning_peak": "08:30", "midday": "12:30",
              "evening_peak": "18:30", "night": "22:00"},
    "days": "*",                        # e.g. "sat,sun,mon,tue,wed,thu" to skip Friday
    # Low-volume mode: each slot quotes only one group of routes, and the groups
    # rotate daily, so every route visits every slot over len(slots) days.
    # 12 routes / 4 slots = 3 quotes per slot, 12 per day in total.
    "rotate_routes": True,

    "gap_seconds": (40, 90),            # pause between routes
    "launch_wait": 8,                   # after opening the app
    "search_wait": 3,                   # after typing the destination
    "fare_timeout": 30,                 # max wait for prices to appear
    "settle_seconds": 3,                # let prices finish loading
    "max_scrolls": 3,                   # swipes on the ride list to reveal more cards

    # Popups to close if they appear. Never put a booking button here.
    "dismiss_texts": ["Not now", "Skip", "Later", "Close", "Got it", "Maybe later", "No thanks"],
    # Buttons Pathao may show between choosing a destination and the fare list.
    "after_destination_taps": ["Done", "Confirm destination", "Set destination"],
    # Text that means the session is logged out.
    "login_markers": ["enter your phone", "enter phone number", "verify otp", "log in", "sign in"],
}

# Resource-ids seen in Pathao's screens (the part after "com.pathao.user:id/").
RID = {
    "address_input": "etAddress",       # "Where are you going?" box
    "address": "tvAddress",             # pickup line, search results, map labels
    "eta": "tvEta",                     # "Pickup in 2 min" / "Reach in 17 mins"
    "ride_type": "tvRideType",          # "Bike", "CNG", "Car Plus", "Car Prime"
    "seats": "tvPersonCount",
    "fare_original": "tvActualFare",    # struck-through price (before discount)
    "fare": "tvFare",                   # price shown to the rider
    "notice": "tvMessageText",          # "A fee may apply for long distance pickup"
}

# UiAutomator selectors, tried in order.
SEL = {
    "car_entry": [
        'new UiSelector().resourceIdMatches(".*:id/tv\\\\w+Title").text("Car")',
        'new UiSelector().text("Car")',
    ],
    "search_input": [
        'new UiSelector().resourceId("com.pathao.user:id/etAddress")',
        'new UiSelector().className("android.widget.EditText").instance(0)',
    ],
}

# Anything that would dispatch a driver. Pathao's button reads "Choose Bike" / "Choose Car Plus".
FORBIDDEN = re.compile(
    r"(?<![a-z])(choose|request|booking|book|ride[\s_]*now)(?![a-z])"
    r"|confirm[\s_]*(ride|booking|request|pickup|car|bike)", re.I)

BN_DIGITS = str.maketrans("০১২৩৪৫৬৭৮৯", "0123456789")
NUM_RE = re.compile(r"(\d[\d,]*(?:\.\d+)?)")
MIN_RE = re.compile(r"(\d+)\s*(?:min|mins|minutes)\b", re.I)

FIELDS = ["ts", "slot", "route_id", "band", "pickup_label", "pickup_lat", "pickup_lng",
          "pickup_shown", "drop_query", "drop_shown", "drop_lat", "drop_lng",
          "ride_type", "fare_shown", "fare_original", "discount", "is_estimate", "seats",
          "pickup_eta_min", "trip_eta_min", "selected_type", "surge_note", "notice",
          "screenshot", "status", "seconds"]

BASE = Path(__file__).resolve().parent
ROUTES_CSV = BASE / "routes.csv"
DATA = BASE / "data"
OUT_CSV = DATA / "fares.csv"
SHOT_DIR = DATA / "screens"
DUMP_DIR = DATA / "dumps"
TZ = ZoneInfo("Asia/Dhaka")


class BookingGuard(Exception):
    pass


class SessionExpired(Exception):
    pass


def log(msg):
    print(f"[{datetime.now(TZ):%Y-%m-%d %H:%M:%S}] {msg}", flush=True)


def now_iso():
    return datetime.now(TZ).isoformat(timespec="seconds")


# =============================================================== environment
def adb(*args, check=False):
    r = subprocess.run(["adb", "-s", CONFIG["udid"], *args],
                       capture_output=True, text=True, check=check)
    return r.stdout.strip()


def booted():
    return adb("shell", "getprop", "sys.boot_completed") == "1"


def ensure_emulator():
    try:
        if booted():
            return
    except FileNotFoundError:
        raise SystemExit("adb not found: add <Android SDK>/platform-tools to PATH")
    log(f"starting emulator '{CONFIG['avd_name']}'")
    cmd = ["emulator", "-avd", CONFIG["avd_name"], "-no-boot-anim"]
    if CONFIG["headless"]:
        cmd.append("-no-window")
    try:
        subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except FileNotFoundError:
        raise SystemExit("emulator not found: add <Android SDK>/emulator to PATH")
    for _ in range(90):
        time.sleep(4)
        if booted():
            time.sleep(15)              # let Play services settle
            return
    raise RuntimeError("emulator did not finish booting within 6 minutes")


def ensure_appium():
    url = CONFIG["appium_url"].rstrip("/") + "/status"

    def up():
        try:
            urllib.request.urlopen(url, timeout=3)
            return True
        except Exception:
            return False

    if up():
        return
    log("starting Appium server")
    subprocess.Popen(["appium", "--log-level", "warn"], shell=(os.name == "nt"),
                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for _ in range(30):
        time.sleep(2)
        if up():
            return
    raise RuntimeError("Appium server did not start; run `appium` in a terminal to see why")


def prepare_device():
    pkg = CONFIG["app_package"]
    if pkg not in adb("shell", "pm", "list", "packages", pkg):
        raise SystemExit(f"{pkg} is not installed on {CONFIG['udid']} (check app_package)")
    adb("shell", "pm", "grant", pkg, "android.permission.ACCESS_FINE_LOCATION")
    adb("shell", "pm", "grant", pkg, "android.permission.ACCESS_COARSE_LOCATION")
    adb("shell", "settings", "put", "secure", "location_mode", "3")  # high accuracy


def new_driver():
    o = UiAutomator2Options()
    o.platform_name = "Android"
    o.udid = CONFIG["udid"]
    o.no_reset = True                   # keep the logged-in Pathao session
    o.new_command_timeout = 600
    return webdriver.Remote(CONFIG["appium_url"], options=o)


def set_gps(lat, lng):
    for _ in range(2):                  # twice: the first fix is sometimes ignored
        adb("emu", "geo", "fix", str(lng), str(lat))   # longitude first
        time.sleep(1.5)


# =============================================================== UI helpers
def ui(driver, selector):
    return driver.find_elements(AppiumBy.ANDROID_UIAUTOMATOR, selector)


def by_rid(driver, key):
    return driver.find_elements(AppiumBy.ID, f"{CONFIG['app_package']}:id/{RID[key]}")


def find_any(driver, key, timeout=15):
    end = time.time() + timeout
    while time.time() < end:
        for s in SEL[key]:
            els = ui(driver, s)
            if els:
                return els[0]
        time.sleep(0.7)
    raise LookupError(f"could not find '{key}' - check SEL['{key}'] using `dump`")


def safe_click(el):
    label = " ".join(x for x in (el.text, el.get_attribute("content-desc"),
                                 el.get_attribute("resource-id")) if x)
    if FORBIDDEN.search(label):
        raise BookingGuard(f"refused to tap a booking control: {label!r}")
    el.click()


def tap_if_present(driver, texts, rounds=2):
    for _ in range(rounds):
        tapped = False
        for t in texts:
            els = ui(driver, f'new UiSelector().text("{t}")')
            if els:
                safe_click(els[0])
                tapped = True
                time.sleep(1)
        if not tapped:
            return


def screen_texts(xml):
    root = ET.fromstring(xml.encode("utf-8"))
    return [((n.get("text") or "").strip() or (n.get("content-desc") or "").strip())
            for n in root.iter()]


def check_logged_in(driver):
    blob = " | ".join(t for t in screen_texts(driver.page_source) if t).lower()
    if any(m in blob for m in CONFIG["login_markers"]):
        raise SessionExpired("Pathao is on a login screen - log in by hand, then rerun")


def surge_texts(xml):
    """Any banner whose resource-id mentions surge, e.g. 'Fares are now lower for Bike'."""
    out = []
    for n in ET.fromstring(xml.encode("utf-8")).iter():
        if "surge" in (n.get("resource-id") or "").lower() and (n.get("text") or "").strip():
            out.append(n.get("text").strip())
    return " / ".join(dict.fromkeys(out))


# =============================================================== fare parsing
def money(text):
    m = NUM_RE.search((text or "").translate(BN_DIGITS))
    return float(m.group(1).replace(",", "")) if m else ""


def minutes(text):
    m = MIN_RE.search((text or "").translate(BN_DIGITS))
    return int(m.group(1)) if m else ""


def parse_ride_screen(xml):
    """Read Pathao's Ride Details screen. Returns (cards by ride type, screen-level info)."""
    cards, meta, cur, last_eta = {}, {}, None, ""
    for n in ET.fromstring(xml.encode("utf-8")).iter():
        rid = (n.get("resource-id") or "").split(":id/")[-1]
        t = (n.get("text") or "").strip()
        if not t:
            continue
        if t.lower().startswith("choose "):                  # the booking button
            meta["selected_type"] = t[7:].strip()
        elif rid == RID["eta"]:
            last_eta = t
        elif rid == RID["address"] and last_eta:
            if last_eta.lower().startswith("pickup"):
                meta["pickup_shown"], meta["pickup_eta_min"] = t, minutes(last_eta)
            elif last_eta.lower().startswith("reach"):
                meta["drop_shown"], meta["trip_eta_min"] = t, minutes(last_eta)
            last_eta = ""
        elif rid == RID["notice"]:
            meta["notice"] = t
        elif rid == RID["ride_type"]:
            cur = cards.setdefault(t, {"ride_type": t, "fare_shown": "", "fare_original": "",
                                       "is_estimate": "", "seats": ""})
        elif cur is not None and rid == RID["seats"]:
            cur["seats"] = t
        elif cur is not None and rid == RID["fare_original"]:
            cur["fare_original"] = money(t)
        elif cur is not None and rid == RID["fare"]:
            cur["fare_shown"] = money(t)
            cur["is_estimate"] = int(t.startswith("~"))      # "~৳217" = approximate
    for c in cards.values():
        if c["fare_original"] != "" and c["fare_shown"] != "":
            c["discount"] = round(c["fare_original"] - c["fare_shown"], 2)
    s = surge_texts(xml)
    if s:
        meta["surge_note"] = s
    return cards, meta


def priced(cards):
    return {k for k, v in cards.items() if v["fare_shown"] != ""}


def read_fare_screen(driver, shot_path):
    end = time.time() + CONFIG["fare_timeout"]
    while True:
        cards, meta = parse_ride_screen(driver.page_source)
        if priced(cards):
            break
        if time.time() > end:
            raise TimeoutError("fare screen never showed prices")
        time.sleep(1)
    time.sleep(CONFIG["settle_seconds"])
    driver.save_screenshot(str(shot_path))
    cards, meta = parse_ride_screen(driver.page_source)

    size = driver.get_window_size()
    w, h = size["width"], size["height"]
    for _ in range(CONFIG["max_scrolls"]):       # reveal ride cards below the fold
        before = priced(cards)
        # swipe inside the ride list only (45%-75% of the height), away from the buttons
        driver.execute_script("mobile: swipeGesture", {
            "left": int(w * 0.1), "top": int(h * 0.45),
            "width": int(w * 0.8), "height": int(h * 0.30),
            "direction": "up", "percent": 0.7})
        time.sleep(1.2)
        more, more_meta = parse_ride_screen(driver.page_source)
        for k, v in more.items():
            if k not in cards or (cards[k]["fare_shown"] == "" and v["fare_shown"] != ""):
                cards[k] = v
        for k, v in more_meta.items():
            meta.setdefault(k, v)
        if priced(cards) == before:
            break
    keep, skip = CONFIG["keep_types"], CONFIG["skip_types"]
    cards = {k: v for k, v in cards.items()
             if k not in skip and (not keep or k in keep)}
    return cards, meta


# =============================================================== one route
def pick_result(driver, match, below_y):
    """Tap the first search result below the input box whose text contains `match`."""
    for el in by_rid(driver, "address"):
        if el.rect["y"] > below_y and match.lower() in (el.text or "").lower():
            safe_click(el)
            return el.text
    shown = [e.text for e in by_rid(driver, "address") if e.rect["y"] > below_y]
    raise LookupError(f"no result containing '{match}'; results were {shown[:6]}")


def quote_route(driver, r, slot):
    t0 = time.time()
    pkg = CONFIG["app_package"]
    row = {k: r.get(k, "") for k in ("route_id", "band", "pickup_label", "pickup_lat",
                                     "pickup_lng", "drop_query", "drop_lat", "drop_lng")}
    row.update(ts=now_iso(), slot=slot)

    driver.terminate_app(pkg)
    set_gps(r["pickup_lat"], r["pickup_lng"])
    driver.activate_app(pkg)
    time.sleep(CONFIG["launch_wait"])
    tap_if_present(driver, CONFIG["dismiss_texts"])
    check_logged_in(driver)

    safe_click(find_any(driver, "car_entry"))           # opens the destination search
    time.sleep(2)
    tap_if_present(driver, CONFIG["dismiss_texts"])

    box = find_any(driver, "search_input")
    safe_click(box)
    box.clear()
    box.send_keys(r["drop_query"])
    time.sleep(CONFIG["search_wait"])
    rect = box.rect
    search_surge = surge_texts(driver.page_source)
    pick_result(driver, r.get("result_match") or r["drop_query"], rect["y"] + rect["height"])
    time.sleep(2)
    tap_if_present(driver, CONFIG["after_destination_taps"])

    shot = SHOT_DIR / f"{row['ts'].replace(':', '')[:15]}_{r['route_id']}.png"
    cards, meta = read_fare_screen(driver, shot)
    if search_surge:
        meta["surge_note"] = " / ".join(x for x in (search_surge, meta.get("surge_note")) if x)
    row.update(meta, screenshot=shot.name, seconds=round(time.time() - t0))
    driver.back()                                        # leave the fare screen
    if not cards:
        return [dict(row, status="no_ride_cards_parsed")]
    return [dict(row, **c, status="ok") for c in cards.values()]


# =============================================================== runs
PENDING_CSV = DATA / "fares_pending.csv"


def _append(path, rows):
    new = not path.exists()
    with path.open("a", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
        if new:
            w.writeheader()
        w.writerows(rows)


def write_rows(rows):
    """Append to fares.csv. If Excel has it open (locked), wait; if still locked,
    park the rows in fares_pending.csv and merge them on the next successful write."""
    DATA.mkdir(exist_ok=True)
    pending = []
    if PENDING_CSV.exists():
        try:
            with PENDING_CSV.open(encoding="utf-8-sig") as f:
                pending = list(csv.DictReader(f))
        except PermissionError:
            pending = None
    for attempt in range(10):
        try:
            _append(OUT_CSV, (pending or []) + rows)
            if pending:
                PENDING_CSV.unlink()
                log(f"  merged {len(pending)} parked row(s) into fares.csv")
            return
        except PermissionError:
            if attempt == 0:
                log("  fares.csv is locked (open in Excel?) - close it; retrying for 30s")
            time.sleep(3)
    try:
        _append(PENDING_CSV, rows)
        log("  fares.csv still locked - rows parked in data/fares_pending.csv")
    except PermissionError:
        log("  WARNING: both CSVs locked - these rows were not saved")


def load_routes(only=None):
    with ROUTES_CSV.open(encoding="utf-8-sig") as f:
        routes = [r for r in csv.DictReader(f) if r.get("route_id")]
    if only:
        routes = [r for r in routes if r["route_id"] == only]
        if not routes:
            raise SystemExit(f"route {only} not in routes.csv")
    return routes                        # fixed order: each route hits the same time daily


def routes_for_slot(routes, slot):
    """Latin-square rotation: on day d, slot k gets group (k + d) % n_slots."""
    slots = list(CONFIG["slots"])
    if not CONFIG["rotate_routes"] or slot not in slots:
        return routes
    n = len(slots)
    groups = [routes[i::n] for i in range(n)]
    day = datetime.now(TZ).date().toordinal()
    return groups[(slots.index(slot) + day) % n]


def run_slot(slot, only=None):
    SHOT_DIR.mkdir(parents=True, exist_ok=True)
    ensure_emulator()
    ensure_appium()
    prepare_device()
    routes = load_routes(only) if only else routes_for_slot(load_routes(), slot)
    log(f"slot '{slot}': {len(routes)} route(s)")
    driver = new_driver()
    ok = 0
    try:
        for i, r in enumerate(routes):
            try:
                rows = quote_route(driver, r, slot)
                ok += 1
                x = rows[0]
                log(f"  {r['route_id']} {x.get('pickup_shown', '')} -> {x.get('drop_shown', '')} "
                    f"({x.get('trip_eta_min', '?')} min): " + ", ".join(
                        f"{y.get('ride_type')}={y.get('fare_shown')}" for y in rows))
            except (BookingGuard, SessionExpired) as e:
                write_rows([{"ts": now_iso(), "slot": slot, "route_id": r["route_id"],
                             "status": f"STOPPED: {e}"}])
                log(f"  STOPPED: {e}")
                break
            except Exception as e:
                err = SHOT_DIR / f"ERR_{now_iso().replace(':', '')[:15]}_{r['route_id']}.png"
                try:
                    driver.save_screenshot(str(err))
                except Exception:
                    pass
                rows = [{"ts": now_iso(), "slot": slot, "route_id": r["route_id"],
                         "screenshot": err.name,
                         "status": f"error: {type(e).__name__}: {e}"[:250]}]
                log(f"  {r['route_id']}: {rows[0]['status']}")
            write_rows(rows)
            if i < len(routes) - 1:
                time.sleep(random.uniform(*CONFIG["gap_seconds"]))
    finally:
        try:
            driver.terminate_app(CONFIG["app_package"])
        except Exception:
            pass
        driver.quit()
    log(f"slot '{slot}' done: {ok}/{len(routes)} routes ok")


def run_slot_safe(slot):
    try:
        run_slot(slot)
    except BaseException as e:           # keep the scheduler alive
        log(f"slot '{slot}' failed: {type(e).__name__}: {e}")


def schedule():
    from apscheduler.executors.pool import ThreadPoolExecutor
    from apscheduler.schedulers.blocking import BlockingScheduler
    from apscheduler.triggers.cron import CronTrigger

    # one worker: slots queue instead of fighting over the emulator
    sch = BlockingScheduler(timezone="Asia/Dhaka",
                            executors={"default": ThreadPoolExecutor(1)})
    for slot, hhmm in CONFIG["slots"].items():
        h, m = map(int, hhmm.split(":"))
        sch.add_job(run_slot_safe, CronTrigger(hour=h, minute=m, day_of_week=CONFIG["days"],
                                               timezone="Asia/Dhaka"),
                    args=[slot], id=slot, max_instances=1, coalesce=True,
                    misfire_grace_time=900)
    log("scheduler running: " + ", ".join(f"{s} {t}" for s, t in CONFIG["slots"].items()))
    log("leave this window open; Ctrl+C to stop")
    sch.start()


def dump():
    ensure_emulator()
    ensure_appium()
    DUMP_DIR.mkdir(parents=True, exist_ok=True)
    d = new_driver()
    try:
        stamp = now_iso().replace(":", "")[:15]
        src = d.page_source
        (DUMP_DIR / f"{stamp}.xml").write_text(src, encoding="utf-8")
        d.save_screenshot(str(DUMP_DIR / f"{stamp}.png"))
        for n in ET.fromstring(src.encode("utf-8")).iter():
            t, desc = n.get("text") or "", n.get("content-desc") or ""
            if t.strip() or desc.strip():
                cls = (n.get("class") or "").split(".")[-1]
                print(f"{cls:16} text={t!r:40} desc={desc!r:24} "
                      f"id={n.get('resource-id') or ''} clickable={n.get('clickable')}")
        cards, meta = parse_ride_screen(src)
        if cards:
            print("\nparsed:", meta)
            for c in cards.values():
                print("  ", c)
        log(f"saved data/dumps/{stamp}.xml and .png")
    finally:
        d.quit()


def main():
    ap = argparse.ArgumentParser(description="Pathao fare-quote logger")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("dump")
    p1 = sub.add_parser("once")
    p1.add_argument("--route", required=True)
    p2 = sub.add_parser("run")
    p2.add_argument("--slot", default="manual")
    sub.add_parser("schedule")
    a = ap.parse_args()

    if a.cmd == "dump":
        dump()
    elif a.cmd == "once":
        run_slot("test", only=a.route)
    elif a.cmd == "run":
        run_slot(a.slot)
    else:
        schedule()


if __name__ == "__main__":
    main()

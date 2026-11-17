#!/usr/bin/env python3
"""Kongfang compset collector.

Reads each property's public direct-booking engine and records, for every
night from today forward:
  sold   = units no longer bookable (total - still available)
  total  = units the property has
  price  = average of the lowest public rate per room type that night
           (None when nothing is on sale, e.g. sold out)
Writes:
  compset/data/latest.json              full snapshot used by the dashboard
  compset/data/history/YYYY-MM-DD.json  compact "sold" snapshot per day (pickup)
  compset/data/history/index.json       list of snapshot dates

Only the Python standard library is used.
"""
import datetime as dt
import gzip
import http.cookiejar
import json
import os
import re
import statistics
import sys
import time
import urllib.parse
import urllib.request
from html.parser import HTMLParser

HORIZON_DAYS = int(os.environ.get("HORIZON_DAYS", "120"))
BKK = dt.timezone(dt.timedelta(hours=7))
TODAY = dt.datetime.now(BKK).date()
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/130.0 Safari/537.36")

jar = http.cookiejar.CookieJar()
opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(jar))


def req(url, data=None, headers=None, tries=3):
    h = {"User-Agent": UA, "Accept": "*/*", "Accept-Encoding": "gzip"}
    h.update(headers or {})
    if isinstance(data, str):
        data = data.encode()
    last = None
    for i in range(tries):
        try:
            r = opener.open(urllib.request.Request(url, data=data, headers=h), timeout=40)
            raw = r.read()
            if r.headers.get("Content-Encoding") == "gzip":
                raw = gzip.decompress(raw)
            return raw.decode("utf-8", "replace")
        except Exception as e:  # noqa: BLE001
            last = e
            time.sleep(2 + 3 * i)
    raise last


def nights():
    return [TODAY + dt.timedelta(days=i) for i in range(HORIZON_DAYS)]


def iso(d):
    return d.isoformat()


def avg_price(values):
    vals = [float(v) for v in values if v and float(v) > 0]
    return round(statistics.mean(vals)) if vals else None


def chunks(days):
    end = TODAY + dt.timedelta(days=HORIZON_DAYS - 1)
    start = TODAY
    while start <= end:
        stop = min(end, start + dt.timedelta(days=days - 1))
        yield start, stop
        start = stop + dt.timedelta(days=1)


# ---------------------------------------------------------------- SiteMinder
def siteminder(channel, room_caps):
    """room_caps: {room_type_id: units}."""
    # The API pads results out to whole months, so chunks overlap: keep one
    # value per (room type, date) and only dates inside the horizon.
    wanted = {iso(d) for d in nights()}
    avail, price = {}, {}
    for start, stop in chunks(60):
        for rt, cap in room_caps.items():
            url = (f"https://book-directonline.com/api/properties/{channel}/room-types/{rt}/availability"
                   f"?checkInsFrom={iso(start)}&checkInsTo={iso(stop)}&adults=2&children=0&infants=0&los=1")
            for x in json.loads(req(url))["result"]:
                d = x["date"][:10]
                if d in wanted:
                    avail[(rt, d)] = min(cap, max(0, int(x.get("totalAvailability") or 0)))
                    price[(rt, d)] = x.get("price") or 0
    total = sum(room_caps.values())
    out = {}
    for d in sorted(wanted):
        if all((rt, d) in avail for rt in room_caps):
            out[d] = [total - sum(avail[(rt, d)] for rt in room_caps), total,
                      avg_price(price.get((rt, d)) for rt in room_caps)]
    return out


# ---------------------------------------------------------------- Cloudbeds
YATIKA_CAPS = {
    "41565889478835": 1, "41566837260435": 1, "41567362044103": 1, "37933102436562": 1,
    "41311044653248": 1, "41318110138553": 1, "41321436131459": 1, "41322908328142": 1,
    "41350131904763": 2, "41352310792443": 2, "41551923912912": 1, "41553578668165": 1,
    "41554955587831": 1, "41558214742206": 1, "41561198002417": 2, "41564005568708": 1,
}


def cloudbeds(slug, prop_id, caps):
    req(f"https://us2.cloudbeds.com/en/reservation/{slug}?currency=thb")  # session cookie
    total = sum(caps.values())
    out = {}
    for d in nights():
        body = urllib.parse.urlencode({
            "checkin": iso(d), "checkout": iso(d + dt.timedelta(days=1)),
            "currency_code": "THB", "widget_property": prop_id, "lang": "en"})
        j = json.loads(req("https://us2.cloudbeds.com/booking/rooms", body, {
            "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
            "X-Requested-With": "XMLHttpRequest",
            "Referer": f"https://us2.cloudbeds.com/en/reservation/{slug}"}))
        left, low = {}, {}
        for x in j.get("room_types", []):
            rid = str(x.get("room_type_id"))
            if rid not in caps:
                continue
            left[rid] = max(left.get(rid, 0), min(caps[rid], int(x.get("remaining") or 0)))
            r = float(x.get("rate_min") or 0)
            if r > 0:
                low[rid] = min(low.get(rid, r), r)
        out[iso(d)] = [total - sum(left.values()), total, avg_price(low.values())]
        time.sleep(0.4)
    return out


# ---------------------------------------------------------------- Roomscope
TH_MONTHS = ["ม.ค.", "ก.พ.", "มี.ค.", "เม.ย.", "พ.ค.", "มิ.ย.",
             "ก.ค.", "ส.ค.", "ก.ย.", "ต.ค.", "พ.ย.", "ธ.ค."]


class _RSParser(HTMLParser):
    """Reads the per-room-type availability list and the 'from' price boxes."""

    def __init__(self):
        super().__init__()
        self.in_list = False
        self.cur = None
        self.capture = None
        self.items = {}
        self.in_price = 0
        self.price_buf = []
        self.prices = []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        cls = a.get("class") or ""
        if tag == "ul" and a.get("id") == "availability-room":
            self.in_list = True
        if self.in_list:
            if tag == "a" and (a.get("href") or "").startswith("#jump_roomtype_"):
                self.cur = a["href"].split("_")[-1]
            if tag == "span" and "number-of" in cls and self.cur:
                self.capture = self.cur
        if tag == "div" and "room-price-available" in cls:
            self.in_price = 1
            self.price_buf = []
        elif tag == "div" and self.in_price:
            self.in_price += 1

    def handle_endtag(self, tag):
        if tag == "ul" and self.in_list:
            self.in_list = False
        if tag == "div" and self.in_price:
            self.in_price -= 1
            if self.in_price == 0:
                m = re.search(r"฿\s*([\d,]+)", "".join(self.price_buf))
                if m:
                    self.prices.append(int(m.group(1).replace(",", "")))

    def handle_data(self, data):
        if self.in_price:
            self.price_buf.append(data)
        if self.capture and data.strip():
            try:
                self.items[self.capture] = int(data.strip())
            except ValueError:
                pass
            self.capture = None
            self.cur = None


def roomscope(hotel, caps):
    total = sum(caps.values())
    out = {}
    for d in nights():
        fields = [("Filter.DisplayType", "Rsvn"), ("ServiceType", "Building"),
                  ("Filter.CheckIn", f"{d.day} {TH_MONTHS[d.month - 1]} {d.year}"),
                  ("Filter.NumNight", "1")] + [("Filter.SelectedRoomTypes", k) for k in caps]
        html = req(f"https://reservation.roomscope.co/{hotel}/th/rsvn/getinventory?d={int(time.time()*1000)}",
                   urllib.parse.urlencode(fields), {
                       "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
                       "X-Requested-With": "XMLHttpRequest"})
        p = _RSParser()
        p.feed(html)
        avail = sum(min(caps[k], v) for k, v in p.items.items() if k in caps)
        out[iso(d)] = [total - avail, total, avg_price(p.prices)]
        time.sleep(0.4)
    return out


# ---------------------------------------------------------------- ZUZU (zoombookdirect)
def zuzu(hotel_id, engine_code):
    wanted = {iso(d) for d in nights()}
    rows, low = {}, {}
    for start, stop in chunks(30):
        j = json.loads(req(f"https://avail.zuzuhs.com/hotels/{hotel_id}/availability/v1"
                           f"?from_date={iso(start)}&to_date={iso(stop)}"))
        for x in j.get("availabilities", []):
            d = x["date"][:10]
            if x.get("is_active") and d in wanted:
                c = int(x.get("count") or 0)
                rows[(x.get("room_type_id"), d)] = (c - int(x.get("available_count") or 0), c)
        try:
            p = json.loads(req(
                f"https://booking-engine.zoombookdirect.com/booking-engine/hotel/{engine_code}/room-rate-prices"
                f"?from_date={iso(start)}&to_date={iso(stop)}&channel_id=98&max_promotion_limit=2"
                f"&guest_count=2&room_count=1&channel_manager_id=2"))
            for x in p.get("room_rate_prices", []):
                d = x["date"][:10]
                if d in wanted and x.get("min_rate"):
                    low[(x.get("room_type_id"), d)] = float(x["min_rate"])
        except Exception:  # noqa: BLE001  prices are optional
            pass
    out = {}
    for (_, d), (sold, c) in rows.items():
        o = out.setdefault(d, [0, 0, None])
        o[0] += sold
        o[1] += c
    for d in out:
        out[d][2] = avg_price(v for (rt, dd), v in low.items() if dd == d)
    return dict(sorted(out.items()))


# ---------------------------------------------------------------- Pukdee
def pukdee(slug, client_id):
    out = {}
    for d in nights():
        j = json.loads(req("https://pukdee.com/booking/api.php?action=get_available_rooms",
                           json.dumps({"client_id": client_id, "checkin": iso(d),
                                       "checkout": iso(d + dt.timedelta(days=1))}),
                           {"Content-Type": "application/json",
                            "Referer": f"https://pukdee.com/booking/{slug}"}))
        a = t = 0
        prices = []
        for r in j.get("rooms", []):
            a += int(r.get("available_qty") or 0)
            t += int(r.get("total_qty") or 0)
            prices.append(r.get("price"))
        out[iso(d)] = [t - a, t, avg_price(prices)]
        time.sleep(0.4)
    return out


PROPERTIES = [
    {"id": "kongfang", "name": "กองฟาง", "units": 4, "self": True,
     "fn": lambda: siteminder("kongfangwildernessretreat", {"307157": 2, "307159": 2})},
    {"id": "azalea", "name": "Azalea Village", "units": 21,
     "fn": lambda: pukdee("azalea", 1)},
    {"id": "mist", "name": "Mist Villa", "units": 7,
     "fn": lambda: zuzu(6435, "019D42B5BDE47DE496F140A34678")},
    {"id": "yatika", "name": "Yatika Boutique", "units": 19,
     "fn": lambda: cloudbeds("HkgYM3", "33241915482304", YATIKA_CAPS)},
    {"id": "lagom", "name": "LAGÖM Village", "units": 7,
     "fn": lambda: roomscope(2256, {"36587": 1, "36596": 1, "36641": 3, "36588": 1, "42452": 1})},
    {"id": "luanglume", "name": "Luang Lume", "units": 6,
     "fn": lambda: siteminder("luanglumepoolvilla", {"326288": 1, "326289": 1, "326290": 4})},
]


def main():
    os.makedirs(os.path.join(DATA, "history"), exist_ok=True)
    latest_path = os.path.join(DATA, "latest.json")
    prev = {}
    if os.path.exists(latest_path):
        with open(latest_path, encoding="utf-8") as f:
            prev = json.load(f)
    prev_by_id = {p["id"]: p for p in prev.get("properties", [])}

    result = {"collected_at": dt.datetime.now(BKK).isoformat(timespec="minutes"),
              "today": iso(TODAY), "properties": []}
    failures = 0
    for p in PROPERTIES:
        meta = {k: v for k, v in p.items() if k != "fn"}
        t0 = time.time()
        try:
            nightly = p["fn"]()
            if not nightly:
                raise RuntimeError("no nights returned")
            meta.update(status="ok", nightly=dict(sorted(nightly.items())),
                        seconds=round(time.time() - t0, 1))
        except Exception as e:  # noqa: BLE001
            failures += 1
            old = prev_by_id.get(p["id"], {})
            meta.update(status="error", error=f"{type(e).__name__}: {e}"[:300],
                        nightly=old.get("nightly", {}),
                        stale_since=old.get("stale_since") or prev.get("collected_at"))
        print(f"{p['id']:<10} {meta['status']:<6} {len(meta['nightly'])} nights", file=sys.stderr)
        result["properties"].append(meta)

    with open(latest_path, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, separators=(",", ":"))

    snap = {"date": iso(TODAY), "sold": {
        p["id"]: {d: v[0] for d, v in p["nightly"].items()}
        for p in result["properties"] if p["status"] == "ok"}}
    hist = os.path.join(DATA, "history")
    with open(os.path.join(hist, f"{iso(TODAY)}.json"), "w", encoding="utf-8") as f:
        json.dump(snap, f, separators=(",", ":"))
    idx = sorted(fn[:-5] for fn in os.listdir(hist) if fn.endswith(".json") and fn != "index.json")
    with open(os.path.join(hist, "index.json"), "w", encoding="utf-8") as f:
        json.dump(idx, f)

    if failures == len(PROPERTIES):
        sys.exit(1)


if __name__ == "__main__":
    main()

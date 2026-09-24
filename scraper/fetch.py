#!/usr/bin/env python3
"""
Polk County (Florida) Motivated Seller Lead Scraper
===================================================
Cloned from the Bexar/Milwaukee/Racine systems; same pipeline:
    scrape -> normalize -> hash/dedupe -> NEW/CHANGED detection -> score -> export

County-specific sources (Polk's recorder search is a NewVision "browserviewor"
app whose JSON API takes RSA-encrypted parameters; the public key is embedded
in the site's own JS, so we encrypt with the same key):

  Official records : https://apps.polkcountyclerk.net/browserviewor/api/search
      - LP / L PEN / A L PEN                  -> Lis Pendens          (cat LP)
      - FIN JDG / JDG / JUD / SUM JDG / CCJ   -> Judgments            (cat JUD)
      - TX LIEN/TX LN/TX WAR/E TX LN/LIEN/
        CE LN/BC LN/AM LN/PG LN/DR LN/CSUP/FF LN -> Liens             (cat LIEN)
      - TDNOT / ATDNOT / TX DEED              -> Tax deed activity    (cat TAXDEED)
      - PROBATE / PRO / WILL  (60-day)        -> Probate / estate     (cat PRO)
      Result rows are one row per indexed party: D = direct (plaintiff /
      lienor / filer), R = reverse (defendant / property owner).  Rows are
      grouped by file number; owner = first R party, grantee = first D party.
      The API caps at ~1000 rows and has no pagination, so windows that hit
      the cap are split recursively.
  Foreclosure sales : https://polk.realforeclose.com  (RealAuction calendar,
      cat FC) -- calendar with selCalDate is server-rendered; auction items
      come from the JSON endpoint index.cfm?zaction=AUCTION&Zmethod=UPDATE&
      FNC=LOAD&AREA=W|C after visiting the PREVIEW page for the date (session
      cursor); retHTML is @-token compressed HTML.
  Tax deed sales    : https://polk.realtaxdeed.com  (same protocol, cat TAXDEED)
  Parcel data       : FL DOR statewide cadastral (services9.arcgis.com,
      Florida_Statewide_Cadastral/FeatureServer/0, CO_NO=53 = Polk):
      OWN_NAME ('LAST FIRST M' uppercase), OWN_ADDR1/OWN_CITY/OWN_STATE_/
      OWN_ZIPCD mailing, PHY_ADDR1/PHY_CITY/PHY_ZIPCD situs, PARCEL_ID, JV.

Run:
    python scraper/fetch.py                # default 7-day lookback
    python scraper/fetch.py --days 14
    python scraper/fetch.py --skip-parcel
"""
from __future__ import annotations

import argparse
import base64
import csv
import hashlib
import json
import logging
import os
import random
import re
import time
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta
from pathlib import Path

import requests

try:
    from Crypto.Cipher import PKCS1_v1_5
    from Crypto.PublicKey import RSA
except ImportError:  # pragma: no cover
    PKCS1_v1_5 = RSA = None

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
COUNTY = "Polk"
STATE = "FL"

CLERK_BASE = "https://apps.polkcountyclerk.net/browserviewor"
CLERK_SEARCH_URL = f"{CLERK_BASE}/api/search"
CLERK_APP_URL = f"{CLERK_BASE}/"

# RSA public key embedded in the clerk site's Scripts/app/services.js --
# the browser encrypts DocTypes/FromDate/ToDate with it (JSEncrypt =
# RSA PKCS#1 v1.5); we do the same.
CLERK_PUBKEY_PEM = (
    "-----BEGIN PUBLIC KEY-----\n"
    "MIGfMA0GCSqGSIb3DQEBAQUAA4GNADCBiQKBgQDXBPCKXRqaD74rYrPXU/DA4Z5H\n"
    "mJbNivwCYijae6QXu/QLqS3GbyGrxkrEmdODbYWOLJfWBvaQSALcolSyKQUvtkjz\n"
    "g61bJC2/xNk4HTHFrA4uAMMvC+49RlSgtEm5dI10+YOp0TGId1d4E0Ey0RDQxNWa\n"
    "ev2TeleyipADuctnqwIDAQAB\n"
    "-----END PUBLIC KEY-----"
)

RF_BASE = "https://polk.realforeclose.com"
RTD_BASE = "https://polk.realtaxdeed.com"

PARCEL_API_URL = ("https://services9.arcgis.com/Gh9awoU677aKree0/arcgis/rest/"
                  "services/Florida_Statewide_Cadastral/FeatureServer/0/query")
POLK_CO_NO = 53  # FL DOR county number for Polk

LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "7"))
PROBATE_LOOKBACK_DAYS = 60   # probate filings move slow; widen window
REQUEST_TIMEOUT = 30
RETRY_COUNT = 3
RETRY_DELAY = 3
CLERK_CAP_SLACK = 1000       # api/search hard cap (observed _max_rows=1000)
ARCGIS_MAX_LOOKUPS = 1500    # cap per-record ArcGIS owner/address lookups
AUCTION_MONTHS_AHEAD = 2     # calendar months to scan on each auction site
AUCTION_MAX_PAGES = 40       # safety cap on AREA paging

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)-8s %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("polk_scraper")

# ---------------------------------------------------------------------------
# Search definitions -> (doc-type codes, category code, human label, probate?)
# Codes discovered live from api/document/doctypes.
# ---------------------------------------------------------------------------
CLERK_QUERIES = [
    ("LP,L PEN,A L PEN",                     "LP",      "Lis Pendens",      False),
    ("FIN JDG,JDG,JUD,SUM JDG,CCJ",          "JUD",     "Judgment",         False),
    ("TX LIEN,TX LN,TX WAR,E TX LN,LIEN,CE LN,BC LN,AM LN,PG LN,DR LN,CSUP,FF LN",
                                             "LIEN",    "Lien",             False),
    ("TDNOT,ATDNOT,TX DEED",                 "TAXDEED", "Tax Deed",         False),
    ("PROBATE,PRO,WILL",                     "PRO",     "Probate / Estate", True),
]
PROBATE_CATS = {"PRO"}

# Friendly names for the raw clerk doc-type codes (for the doc_type column).
DOCTYPE_NICE = {
    "LP": "LIS PENDENS", "L PEN": "LIS PENDENS", "A L PEN": "AMENDED LIS PENDENS",
    "FIN JDG": "FINAL JUDGMENT", "JDG": "JUDGMENT", "JUD": "JUDGMENT",
    "SUM JDG": "SUMMARY JUDGMENT", "CCJ": "CERTIFIED COURT JUDGMENT",
    "TX LIEN": "TAX LIEN", "TX LN": "TAX LIEN", "TX WAR": "TAX WARRANT",
    "E TX LN": "ESTATE TAX LIEN", "LIEN": "LIEN",
    "CE LN": "CODE ENFORCEMENT LIEN", "BC LN": "COUNTY COMMISSIONERS LIEN",
    "AM LN": "AMBULANCE LIEN", "PG LN": "HOSPITAL LIEN",
    "DR LN": "DOMESTIC RELATIONS LIEN", "CSUP": "CHILD SUPPORT",
    "FF LN": "FINE & FORFEITURE LIEN",
    "TDNOT": "NOTICE OF TAX DEED APPLICATION",
    "ATDNOT": "AMENDED NOTICE OF TAX DEED APP", "TX DEED": "TAX DEED",
    "PROBATE": "PROBATE", "PRO": "PROBATE DOCUMENTS", "WILL": "WILL",
}

# ---------------------------------------------------------------------------
# Data model  (identical to Bexar -- required by the dashboard data contract)
# ---------------------------------------------------------------------------
GHL_FIELDS = [
    "doc_num","doc_type","cat","cat_label","filed","owner","grantee",
    "amount","prop_address","prop_city","prop_state","prop_zip",
    "mail_address","mail_city","mail_state","mail_zip","legal","clerk_url","score","flags",
    "first_seen","status",
]
GHL_HEADERS = {f: f.replace("_", " ").title() for f in GHL_FIELDS}
GHL_HEADERS["first_seen"] = "Date Entered System"
GHL_HEADERS["status"] = "Status"

@dataclass
class LeadRecord:
    doc_num: str = ""
    doc_type: str = ""
    cat: str = ""
    cat_label: str = ""
    filed: str = ""
    owner: str = ""
    grantee: str = ""
    amount: float = 0.0
    legal: str = ""
    prop_address: str = ""
    prop_city: str = ""
    prop_state: str = STATE
    prop_zip: str = ""
    mail_address: str = ""
    mail_city: str = ""
    mail_state: str = STATE
    mail_zip: str = ""
    clerk_url: str = ""
    flags: list = field(default_factory=list)
    score: int = 0
    status: str = ""
    first_seen: str = ""
    rid: str = ""
    content_hash: str = ""

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def normalize_date(raw: str) -> str:
    s = str(raw or "").strip()
    if "T" in s:  # ISO timestamps from the clerk API: 2026-09-18T00:00:00
        s = s.split("T", 1)[0]
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y"):
        try:
            return datetime.strptime(s, fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    return s


def _norm_ws(s) -> str:
    return re.sub(r"\s+", " ", str(s or "").strip())


def _sql_lit(s: str) -> str:
    return s.upper().replace("'", "''")


ENTITY_PAT = re.compile(
    r"\b(LLC|L\.L\.C\.|INC|INCORPORATED|CORP|CORPORATION|LTD|LP\b|LLP|"
    r"BANK|MORTGAGE|LENDERS?|CREDIT UNION|FINANCIAL|FUND|TRUST|ESTATE OF|"
    r"ASSOCIATION|COMPANY|CO\.|ENTERPRISES|HOLDINGS|PARTNERS|GROUP|"
    r"N\.?A\.?$|PLLC|PC|CITY OF|COUNTY OF|STATE OF|DEPT|DEPARTMENT|"
    r"AUTHORITY|CHURCH|MINISTRIES|PROPERTIES|INVESTMENTS|VENTURES|"
    r"HOMEOWNERS|CONDOMINIUM|SUPPLY|BUILDERS|CONSTRUCTION|EXPRESS|"
    r"UNITED STATES|FLORIDA|SOLUTIONS|SERVICES|CAPITAL)\b",
    re.IGNORECASE,
)

def is_entity(name: str) -> bool:
    return bool(ENTITY_PAT.search(name or ""))


AKA_PAT = re.compile(r"\s+(?:a/?k/?a|f/?k/?a|d/?b/?a|n/?k/?a)\s+.*$", re.IGNORECASE)
ETAL_PAT = re.compile(r"\s*,?\s*et\s+al\.?\s*$", re.IGNORECASE)
SUFFIX_PAT = re.compile(r"\b(JR|SR|II|III|IV|V)\.?$", re.IGNORECASE)


def split_index_name(name: str) -> tuple:
    """Clerk index names are 'LAST FIRST [MIDDLE...]' uppercase, no comma
    ('AGUILA ROGELIO SAMALEA' -> first='ROGELIO', last='AGUILA').
    Names with a comma are 'LAST, FIRST'.  Entities return ('', name)."""
    n = _norm_ws(name)
    if not n:
        return "", ""
    if is_entity(n):
        return "", n
    n = SUFFIX_PAT.sub("", n).strip(" ,")
    if "," in n:
        last, rest = n.split(",", 1)
        first = rest.strip().split()
        return (first[0] if first else ""), last.strip()
    parts = n.split()
    if len(parts) >= 2:
        return parts[1], parts[0]
    return "", n


def owner_lookup_name(name: str) -> str:
    """Normalize a name to the parcel layer's 'LAST FIRST' uppercase format.
    Clerk index names are already LAST FIRST; handle commas + entities too."""
    n = _norm_ws(name).upper().rstrip(".")
    if not n:
        return ""
    if is_entity(n):
        return re.sub(r"[.,]", "", n)
    n = re.sub(r"\bESTATE OF\b", "", n, flags=re.IGNORECASE).strip()
    n = SUFFIX_PAT.sub("", n).strip(" ,")
    if "," in n:
        last, rest = n.split(",", 1)
        first = rest.strip().split()
        return f"{last.strip()} {first[0]}".strip() if first else last.strip()
    # already 'LAST FIRST [MIDDLE]' -- keep the first two tokens
    parts = re.sub(r"[.,]", "", n).split()
    if len(parts) >= 2:
        return f"{parts[0]} {parts[1]}"
    return n


# Polk County municipalities / CDPs with multi-word names, used to split the
# auction sites' un-delimited "STREET CITY" strings from the end.
MULTIWORD_CITIES = [
    "WINTER HAVEN", "HAINES CITY", "LAKE WALES", "LAKE ALFRED", "POLK CITY",
    "EAGLE LAKE", "FORT MEADE", "BABSON PARK", "LAKE HAMILTON", "HIGHLAND CITY",
    "CYPRESS GARDENS", "INWOOD", "JAN PHYL VILLAGE", "GRENELEFE", "INDIAN LAKE ESTATES",
    "RIVER RANCH", "SAN ANTONIO", "NEW YORK", "LOS ANGELES", "LAS VEGAS",
    "SALT LAKE CITY", "SAN DIEGO", "SAN FRANCISCO",
]
CITY_PREFIXES = {
    "WEST", "EAST", "NORTH", "SOUTH", "NEW", "SAINT", "ST", "FORT", "FT",
    "LAKE", "OAK", "SAN", "SANTA", "LOS", "LAS", "EL", "DE", "DES", "MOUNT",
    "MT", "PORT", "WINTER", "HAINES", "EAGLE", "POLK", "BABSON", "HIGHLAND",
    "CYPRESS", "GLEN", "CEDAR",
}

STREET_SUFFIXES = {
    "ST", "AVE", "AV", "RD", "DR", "LN", "BLVD", "CT", "PL", "WAY", "TER",
    "TERR", "CIR", "PKWY", "HWY", "TRL", "SQ", "PLZ", "BND", "XING", "PASS",
    "RUN", "ROW", "WALK", "PATH", "LOOP", "PT", "CV", "EXPY",
}

US_STATES = {
    "AL","AK","AZ","AR","CA","CO","CT","DE","FL","GA","HI","ID","IL","IN",
    "IA","KS","KY","LA","ME","MD","MA","MI","MN","MS","MO","MT","NE","NV",
    "NH","NJ","NM","NY","NC","ND","OH","OK","OR","PA","RI","SC","SD","TN",
    "TX","UT","VT","VA","WA","WV","WI","WY","DC","PR","VI","GU","AS","MP",
}

def parse_mail_addr(raw: str) -> tuple:
    """Parse 'STREET [CITY], ST ZIP' or 'STREET CITY ST ZIP' from the END:
    zip -> state -> city. Returns (street, city, state, zip)."""
    s = _norm_ws(raw).upper()
    if not s:
        return "", "", "", ""
    zip_code = state = city = ""
    m = re.search(r"(\d{5})[- ]?(\d{4})?\s*$", s)
    if m:
        zip_code = m.group(1)
        s = s[:m.start()].strip(" ,")
    m = re.search(r",?\s+([A-Z]{2})\s*$", s)
    if m and m.group(1) in US_STATES:
        state = m.group(1)
        s = s[:m.start()].strip(" ,")
    if "," in s:
        s, city = s.rsplit(",", 1)
        city = city.strip()
        s = s.strip()
    else:
        for mw in MULTIWORD_CITIES:
            if s.endswith(" " + mw):
                city = mw
                s = s[: -len(mw) - 1].strip()
                break
        if not city:
            toks = s.split()
            idx = max((i for i, t in enumerate(toks) if t.rstrip(".") in STREET_SUFFIXES),
                      default=-1)
            tail = toks[idx + 1:] if 0 <= idx < len(toks) - 1 else []
            while tail and (tail[0] in ("#", "APT", "UNIT", "STE", "SUITE", "FL", "LOT")
                            or tail[0].startswith("#")):
                tail = tail[2:] if len(tail) > 1 and not tail[0].startswith("#") else tail[1:]
            if tail:
                city = " ".join(tail)
                s = " ".join(toks[: len(toks) - len(city.split())])
            elif len(toks) >= 2 and toks[-2] in CITY_PREFIXES:
                city = " ".join(toks[-2:])
                s = " ".join(toks[:-2])
            elif toks:
                city = toks[-1]
                s = " ".join(toks[:-1])
    return s.strip(" ,"), city.title(), state, zip_code

# ---------------------------------------------------------------------------
# Clerk official-records scraper  (browserviewor API; same interface as the
# other counties' ClerkScraper classes)
# ---------------------------------------------------------------------------
class ClerkScraper:
    """Queries the Polk browserviewor api/search endpoint.

    Parameters are RSA-encrypted with the site's public key.  Dates go in as
    ' YYYYMMDD' (leading space -- exactly what the site's own JS sends).  The
    server caps responses at ~1000 rows with no pagination, so any window
    that returns >= the cap is split in half recursively down to single days.
    """

    PROBE_TIMEOUT = 12
    PROBE_ATTEMPTS = 6
    PROBE_WAIT = 120

    def __init__(self, default_start: datetime, default_end: datetime,
                 probate_start: datetime):
        self.default_start = default_start
        self.default_end = default_end
        self.probate_start = probate_start
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": UA,
            "Accept": "application/json, text/plain, */*",
            "Content-Type": "application/json;charset=UTF-8",
            "Origin": "https://apps.polkcountyclerk.net",
            "Referer": CLERK_APP_URL,
        })
        if RSA is None:
            raise RuntimeError("pycryptodome is required (pip install pycryptodome)")
        self._cipher = PKCS1_v1_5.new(RSA.import_key(CLERK_PUBKEY_PEM))
        self._consec_fail = 0

    # -- crypto ------------------------------------------------------------
    def _enc(self, plaintext: str) -> str:
        return base64.b64encode(self._cipher.encrypt(plaintext.encode())).decode()

    def _payload(self, codes: str, start: datetime, end: datetime) -> dict:
        return {
            "MaxRows": 0, "RowsPerPage": 0, "StartRow": 0,
            "DocTypes": self._enc(codes),
            "FromDate": self._enc(" " + start.strftime("%Y%m%d")),
            "ToDate": self._enc(" " + end.strftime("%Y%m%d")),
        }

    # -- availability hardening (CI IPs get blocked intermittently) --------
    def _alive(self) -> bool:
        try:
            r = self.session.post(
                CLERK_SEARCH_URL,
                json=self._payload("LP", self.default_end, self.default_end),
                timeout=self.PROBE_TIMEOUT)
            return r.status_code == 200
        except Exception:
            return False

    def _wait_for_clerk(self) -> bool:
        for attempt in range(1, self.PROBE_ATTEMPTS + 1):
            if self._alive():
                log.info("Clerk API reachable (probe %d)", attempt)
                return True
            if attempt < self.PROBE_ATTEMPTS:
                log.warning("Clerk API unreachable (probe %d/%d) -- waiting %ds",
                            attempt, self.PROBE_ATTEMPTS, self.PROBE_WAIT)
                time.sleep(self.PROBE_WAIT)
        log.error("Clerk API unreachable after %d probes -- skipping official records",
                  self.PROBE_ATTEMPTS)
        return False

    # -- fetch with recursive cap-splitting --------------------------------
    def _fetch_raw(self, codes: str, start: datetime, end: datetime) -> list | None:
        for attempt in range(RETRY_COUNT):
            try:
                r = self.session.post(CLERK_SEARCH_URL,
                                      json=self._payload(codes, start, end),
                                      timeout=REQUEST_TIMEOUT)
                if r.status_code == 200:
                    self._consec_fail = 0
                    return r.json() or []
                log.warning("Clerk %s -> HTTP %s: %s", codes[:20], r.status_code,
                            r.text[:150])
            except Exception as exc:
                log.warning("Clerk %s error (attempt %d): %s", codes[:20],
                            attempt + 1, exc)
            if attempt < RETRY_COUNT - 1:
                time.sleep(RETRY_DELAY + random.random())
        self._consec_fail += 1
        return None

    def _fetch_window(self, codes: str, start: datetime, end: datetime,
                      depth: int = 0) -> list:
        rows = self._fetch_raw(codes, start, end)
        if rows is None:
            return []
        total = rows[0].get("_total_rows", len(rows)) if rows else 0
        cap = rows[0].get("_max_rows", CLERK_CAP_SLACK) if rows else CLERK_CAP_SLACK
        if rows and total >= cap and (end - start).days >= 1 and depth < 8:
            mid = start + (end - start) / 2
            mid = datetime(mid.year, mid.month, mid.day)
            log.info("  window %s..%s hit cap (%d) -- splitting",
                     start.date(), end.date(), total)
            left = self._fetch_window(codes, start, mid, depth + 1)
            right = self._fetch_window(codes, mid + timedelta(days=1), end, depth + 1)
            return left + right
        time.sleep(0.4 + random.random() * 0.3)
        return rows

    # -- row grouping ------------------------------------------------------
    @staticmethod
    def _group_rows(rows: list, cat: str, cat_label: str) -> list:
        by_file: dict[str, list] = {}
        for row in rows:
            fn = _norm_ws(row.get("file_num"))
            if fn:
                by_file.setdefault(fn, []).append(row)
        records = []
        for fn, rws in by_file.items():
            r_names = [_norm_ws(w.get("party_name")) for w in rws
                       if w.get("party_code") == "R" and _norm_ws(w.get("party_name"))]
            d_names = [_norm_ws(w.get("party_name")) for w in rws
                       if w.get("party_code") == "D" and _norm_ws(w.get("party_name"))]
            first = rws[0]
            code = _norm_ws(first.get("doc_type"))
            if cat in PROBATE_CATS:
                owner = (d_names or r_names or [""])[0]
                owner = ETAL_PAT.sub("", AKA_PAT.sub("", owner)).strip(" ,")
                grantee = ""
            else:
                # prefer an individual (non-entity) among the R (owner-side)
                # parties; fall back to the first R, then first D.
                persons = [n for n in r_names if not is_entity(n)]
                owner = (persons or r_names or d_names or [""])[0]
                owner = ETAL_PAT.sub("", AKA_PAT.sub("", owner)).strip(" ,")
                grantee = (d_names or [""])[0]
            book = _norm_ws(first.get("book"))
            page = _norm_ws(first.get("page"))
            legal = _norm_ws(first.get("legal_1"))
            rec = LeadRecord(
                doc_num=fn,
                doc_type=DOCTYPE_NICE.get(code, code) or cat_label.upper(),
                cat=cat, cat_label=cat_label,
                filed=normalize_date(first.get("rec_date") or ""),
                owner=owner, grantee=grantee,
                legal=" | ".join(x for x in (legal, f"BK {book} PG {page}" if book else "") if x),
                clerk_url=CLERK_APP_URL,
            )
            records.append(rec)
        return records

    def run(self) -> list:
        if not self._wait_for_clerk():
            return []
        records: list = []
        for codes, cat, cat_label, is_probate in CLERK_QUERIES:
            if self._consec_fail >= 3:
                log.warning("Clerk: 3 consecutive failures -- re-probing")
                self._consec_fail = 0
                if not self._wait_for_clerk():
                    log.error("Clerk lost mid-run -- aborting remaining queries")
                    break
            start = self.probate_start if is_probate else self.default_start
            rows = self._fetch_window(codes, start, self.default_end)
            recs = self._group_rows(rows, cat, cat_label)
            log.info("  -> %d rows / %d unique records for '%s'",
                     len(rows), len(recs), cat)
            records.extend(recs)
        # a doc can be indexed under several of our code groups; keep first
        seen: set = set()
        out = []
        for r in records:
            if r.doc_num in seen:
                continue
            seen.add(r.doc_num)
            out.append(r)
        log.info("Clerk: %d unique records collected", len(out))
        return out

# ---------------------------------------------------------------------------
# RealAuction foreclosure / tax-deed calendars (polk.realforeclose.com and
# polk.realtaxdeed.com share one protocol)
# ---------------------------------------------------------------------------
_TOKEN_MAP = [  # from the site's own auction.js LoadNewArea()
    ("@A", '<div class="'), ("@B", "</div>"), ("@C", 'class="'),
    ("@D", "<div>"), ("@E", "AUCTION"), ("@F", "</td><td"),
    ("@G", "</td></tr>"), ("@H", "<tr><td "), ("@I", "table"),
    ("@J", 'p_back="NextCheck='), ("@K", 'style="Display:none"'),
    ("@L", "/index.cfm?zaction=auction&zmethod=details&AID="),
]

def _decode_rethtml(ret: str) -> str:
    for tok, rep in _TOKEN_MAP:
        ret = ret.replace(tok, rep)
    return ret


def _strip_tags(html: str) -> str:
    return _norm_ws(re.sub(r"<[^>]+>", " ", html))


AUCTION_FIELD_PAT = re.compile(
    r"(Auction Type|Case #|Final Judgment Amount|Opening Bid|Parcel ID|"
    r"Property Address|Assessed Value|Certificate #|Auction Starts|Auction Status|Sold To):?\s*"
)

def _parse_auction_item(text: str) -> dict:
    """'Auction Type: FORECLOSURE Case #: 2025CA... Parcel ID: ...' -> dict."""
    out = {}
    parts = AUCTION_FIELD_PAT.split(text)
    for i in range(1, len(parts) - 1, 2):
        out[parts[i]] = parts[i + 1].strip(" :|")
    return out


def parse_auction_address(raw: str) -> tuple:
    """'1939 MANATEE DR POINCIANA, FL- 34759' -> (street, city, zip).
    The next line may carry only 'CITY, FL- ZIP'."""
    s = _norm_ws(raw).upper()
    zip_code = ""
    m = re.search(r",?\s*FL\s*-?\s*(\d{5})?\s*$", s)
    if m:
        zip_code = m.group(1) or ""
        s = s[:m.start()].strip(" ,")
    street, city, _st, z2 = parse_mail_addr(s)
    return street, city, zip_code or z2


def _month_starts(count: int):
    d = datetime.now().replace(day=1)
    for _ in range(count):
        yield d
        d = (d + timedelta(days=32)).replace(day=1)


def fetch_realauction(base: str, cat: str, cat_label: str, doc_type: str) -> list:
    """Scrape upcoming (future, unsold) auctions from a RealAuction site."""
    records = []
    s = requests.Session()
    s.headers["User-Agent"] = UA
    today = datetime.now().strftime("%Y-%m-%d")
    try:
        day_ids: list[str] = []
        for mstart in _month_starts(AUCTION_MONTHS_AHEAD):
            cal_url = (f"{base}/index.cfm?zaction=USER&zmethod=CALENDAR"
                       f"&selCalDate=%7Bts%20%27{mstart.strftime('%Y-%m-%d')}"
                       f"%2000:00:00%27%7D")
            r = s.get(cal_url, timeout=REQUEST_TIMEOUT)
            boxes = re.findall(
                r"dayid=['\"](\d{2}/\d{2}/\d{4})['\"][^>]*>(.*?)(?=dayid=|CALBOX CALEND|$)",
                r.text, re.S)
            for day, body in boxes:
                sched = re.search(r'CALSCH["\']>(\d+)', body)
                n_sched = int(sched.group(1)) if sched else 0
                d_iso = datetime.strptime(day, "%m/%d/%Y").strftime("%Y-%m-%d")
                if n_sched > 0 and d_iso >= today:
                    day_ids.append(day)
            time.sleep(0.3)
        day_ids = sorted(set(day_ids))
        log.info("%s: %d upcoming auction days", base.split("//")[1], len(day_ids))
        for day in day_ids:
            s.get(f"{base}/index.cfm?zaction=AUCTION&Zmethod=PREVIEW&AUCTIONDATE={day}",
                  timeout=REQUEST_TIMEOUT)
            seen_ids: set = set()
            blocks: list[str] = []
            for area in ("W", "C"):
                for page in range(AUCTION_MAX_PAGES):
                    url = (f"{base}/index.cfm?zaction=AUCTION&Zmethod=UPDATE&FNC=LOAD"
                           f"&AREA={area}&PageDir={0 if page == 0 else 1}"
                           f"&doR={1 if page == 0 else 0}&tx={int(time.time()*1000)}")
                    rr = s.get(url, timeout=REQUEST_TIMEOUT)
                    m = re.search(r'\{"retHTML".*', rr.text, re.S)
                    if not m:
                        break
                    try:
                        ret = json.loads(m.group(0)).get("retHTML") or ""
                    except Exception:
                        break
                    html = _decode_rethtml(ret)
                    items = re.split(r'(?=<div id="AITEM_)', html)
                    new = 0
                    for it in items:
                        idm = re.match(r'<div id="AITEM_(\d+)"', it)
                        if not idm or idm.group(1) in seen_ids:
                            continue
                        seen_ids.add(idm.group(1))
                        blocks.append(it)
                        new += 1
                    if new == 0:
                        break
                    time.sleep(0.25)
            filed = datetime.strptime(day, "%m/%d/%Y").strftime("%Y-%m-%d")
            for blk in blocks:
                f = _parse_auction_item(_strip_tags(blk))
                status = (f.get("Auction Status") or "").upper()
                if "CANCEL" in status or f.get("Sold To"):
                    continue
                case_no = _norm_ws(f.get("Case #") or f.get("Certificate #"))
                amount = 0.0
                amt_raw = f.get("Final Judgment Amount") or f.get("Opening Bid") or ""
                m2 = re.search(r"[\d,]+\.?\d*", amt_raw)
                if m2:
                    try:
                        amount = float(m2.group(0).replace(",", ""))
                    except ValueError:
                        pass
                street, city, zip_code = parse_auction_address(f.get("Property Address") or "")
                parcel = re.sub(r"\D", "", f.get("Parcel ID") or "")
                rec = LeadRecord(
                    doc_num=case_no,
                    doc_type=doc_type,
                    cat=cat,
                    cat_label=f"{cat_label} (Sale {day})",
                    filed=filed,
                    grantee="",
                    amount=amount,
                    legal=f"Auction {day} | Parcel {parcel or 'n/a'} | "
                          f"Assessed {f.get('Assessed Value') or 'n/a'}",
                    prop_address=street, prop_city=city,
                    prop_state=STATE, prop_zip=zip_code,
                    clerk_url=f"{base}/index.cfm?zaction=AUCTION&Zmethod=PREVIEW&AUCTIONDATE={day}",
                )
                rec.parcel_id = parcel  # transient, for enrichment
                if rec.prop_address or parcel:
                    records.append(rec)
        log.info("%s usable records: %d", base.split("//")[1], len(records))
    except Exception as exc:
        log.warning("RealAuction (%s) error: %s", base, exc)
    return records

# ---------------------------------------------------------------------------
# Parcel enrichment (FL DOR statewide cadastral layer, CO_NO=53)
# ---------------------------------------------------------------------------
PARCEL_OUTFIELDS = ("PARCEL_ID,OWN_NAME,OWN_ADDR1,OWN_ADDR2,OWN_CITY,"
                    "OWN_STATE_,OWN_ZIPCD,PHY_ADDR1,PHY_CITY,PHY_ZIPCD,JV")


def _arcgis_query(session, where: str, count: int = 5) -> list:
    params = {
        "where": f"CO_NO={POLK_CO_NO} AND ({where})",
        "outFields": PARCEL_OUTFIELDS,
        "returnGeometry": "false",
        "f": "json",
        "resultRecordCount": count,
    }
    try:
        r = session.get(PARCEL_API_URL, params=params, timeout=REQUEST_TIMEOUT)
        return r.json().get("features", []) or []
    except Exception as exc:
        log.debug("ArcGIS query error: %s", exc)
        return []


def _zip5(v) -> str:
    s = re.sub(r"\D", "", str(v or ""))
    return s[:5]


def _apply_parcel(rec: LeadRecord, att: dict, fill_prop: bool) -> None:
    if fill_prop and not rec.prop_address:
        situs = _norm_ws(att.get("PHY_ADDR1"))
        if situs:
            rec.prop_address = situs
            rec.prop_city = _norm_ws(att.get("PHY_CITY")).title() or rec.prop_city
            rec.prop_zip = _zip5(att.get("PHY_ZIPCD")) or rec.prop_zip
    if not rec.mail_address:
        ms = _norm_ws(att.get("OWN_ADDR1"))
        if _norm_ws(att.get("OWN_ADDR2")):
            ms = f"{ms} {_norm_ws(att.get('OWN_ADDR2'))}".strip()
        if ms:
            rec.mail_address = ms
            rec.mail_city = _norm_ws(att.get("OWN_CITY")).title()
            rec.mail_state = _norm_ws(att.get("OWN_STATE_")).upper() or STATE
            rec.mail_zip = _zip5(att.get("OWN_ZIPCD"))


def _addr_key(addr: str) -> tuple:
    m = re.match(r"\s*(\d+)\s+(.*)", addr or "")
    if not m:
        return "", ""
    num = m.group(1)
    rest = _norm_ws(m.group(2))
    rest = re.sub(r"\s+(#|APT|UNIT|STE|SUITE|BLDG|LOT)\b.*$", "", rest, flags=re.I).strip()
    return num, rest


def _detect_parcel_format(session) -> bool:
    """True if the layer's PARCEL_ID values contain dashes."""
    feats = _arcgis_query(session, "PARCEL_ID IS NOT NULL", count=1)
    if feats:
        pid = str(feats[0].get("attributes", {}).get("PARCEL_ID") or "")
        log.info("Parcel layer sample PARCEL_ID: %r", pid)
        return "-" in pid
    return False


def enrich_parcels(records: list) -> None:
    session = requests.Session()
    session.headers["User-Agent"] = UA

    # PASS 0 -- exact parcel-id join for auction records.
    pk = [r for r in records if getattr(r, "parcel_id", "")]
    if pk:
        dashed = _detect_parcel_format(session)
        log.info("ArcGIS parcel-join for %d records...", len(pk))
        hits = 0
        for rec in pk:
            pid = rec.parcel_id
            cands = [pid]
            if dashed and len(pid) == 18:
                cands.insert(0, "-".join([pid[0:2], pid[2:4], pid[4:6], pid[6:12], pid[12:18]]))
            feats = []
            for cand in cands:
                feats = _arcgis_query(session, f"PARCEL_ID='{_sql_lit(cand)}'", count=1)
                if feats:
                    break
            if feats:
                att = feats[0].get("attributes", {})
                if not rec.owner:
                    rec.owner = _norm_ws(att.get("OWN_NAME"))
                _apply_parcel(rec, att, fill_prop=True)
                if rec.mail_address:
                    hits += 1
            time.sleep(0.12)
        log.info("ArcGIS parcel-join: %d mailing fills", hits)

    # PASS 1 -- forward by owner name (clerk records have no address at all).
    fwd = [r for r in records if r.owner and (not r.prop_address or not r.mail_address)]
    log.info("ArcGIS owner-lookup for %d records...", len(fwd))
    owner_hits = 0
    for rec in fwd[:ARCGIS_MAX_LOOKUPS]:
        name = owner_lookup_name(rec.owner)
        if not name or len(name) < 5:
            continue
        feats = _arcgis_query(session, f"UPPER(OWN_NAME) LIKE '{_sql_lit(name)}%'")
        if not feats and " " in name and not is_entity(rec.owner):
            last, first = name.split(" ", 1)
            for pat in (f"{last}, {first}%", f"{last}%{first}%"):
                feats = _arcgis_query(session, f"UPPER(OWN_NAME) LIKE '{_sql_lit(pat)}'")
                if feats:
                    break
        if not feats:
            time.sleep(0.12)
            continue
        att = feats[0].get("attributes", {})
        strict = rec.cat in PROBATE_CATS
        unique = len(feats) == 1
        _apply_parcel(rec, att, fill_prop=(unique or not strict) and unique)
        if rec.mail_address:
            owner_hits += 1
        time.sleep(0.12)
    log.info("ArcGIS owner-lookup: %d fills", owner_hits)

    # PASS 2 -- reverse by address (auction records with address, no owner).
    rev = [r for r in records if r.prop_address and not r.owner]
    log.info("ArcGIS address-lookup for %d records...", len(rev))
    addr_hits = 0
    for rec in rev[:ARCGIS_MAX_LOOKUPS]:
        num, core = _addr_key(rec.prop_address)
        if not num or not core:
            continue
        feats = _arcgis_query(session,
                              f"UPPER(PHY_ADDR1) LIKE '{_sql_lit(num)}%{_sql_lit(core)}%'")
        if len(feats) == 1:
            att = feats[0].get("attributes", {})
            owner = _norm_ws(att.get("OWN_NAME"))
            if owner:
                rec.owner = owner
                addr_hits += 1
            _apply_parcel(rec, att, fill_prop=False)
        time.sleep(0.12)
    log.info("ArcGIS address-lookup: %d owner fills", addr_hits)

# ---------------------------------------------------------------------------
# Hash / dedupe identity + NEW-CHANGED detection (pipeline stages 3-4)
# ---------------------------------------------------------------------------
def _repo_base() -> Path:
    return Path(__file__).parent.parent


def _record_rid(r) -> str:
    """Stable identity hash: doc number, else owner|filed|type|address."""
    basis = r.doc_num or f"{r.owner}|{r.filed}|{r.doc_type}|{r.prop_address}"
    return hashlib.sha1(f"polk|{basis}".encode()).hexdigest()[:16]


def _record_chash(r) -> str:
    """Content hash - changes when any meaningful field changes."""
    fields = "|".join(str(x or "") for x in (
        r.doc_num, r.doc_type, r.filed, r.owner, r.grantee, r.legal,
        r.amount, r.prop_address, r.mail_address))
    return hashlib.sha1(fields.encode()).hexdigest()[:16]


def detect_changes(records: list) -> None:
    """Compare against data/state.json; stamp status + first_seen on each record."""
    state_path = _repo_base() / "data" / "state.json"
    try:
        state = json.loads(state_path.read_text(encoding="utf-8")) if state_path.exists() else {}
    except Exception:
        state = {}
    today = datetime.now().strftime("%Y-%m-%d")
    n_new = n_chg = n_exist = 0
    for r in records:
        r.rid = _record_rid(r)
        r.content_hash = _record_chash(r)
        prev = state.get(r.rid)
        if prev is None:
            r.status, r.first_seen = "NEW", today
            n_new += 1
        elif prev.get("content_hash") != r.content_hash:
            r.status = "CHANGED"
            r.first_seen = prev.get("first_seen", today)
            n_chg += 1
        else:
            r.status = "EXISTING"
            r.first_seen = prev.get("first_seen", today)
            n_exist += 1
        state[r.rid] = {"content_hash": r.content_hash,
                        "first_seen": r.first_seen, "last_seen": today}
    state_path.parent.mkdir(parents=True, exist_ok=True)
    state_path.write_text(json.dumps(state, indent=1), encoding="utf-8")
    log.info("NEW/CHANGED: NEW=%d CHANGED=%d EXISTING=%d (state=%d ids)",
             n_new, n_chg, n_exist, len(state))

# ---------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------
def score_records(records: list, start: datetime) -> None:
    for r in records:
        s, flags = 30, []
        if r.cat == "LP": s += 10; flags.append("LIS_PENDENS")
        if r.cat == "FC": s += 15; flags.append("FORECLOSURE")
        if r.cat == "TAXFC": s += 18; flags.append("TAX_FORECLOSURE")
        if r.cat == "TAXDEED": s += 10; flags.append("TAX_DEED")
        if r.cat in ("LP","FC","TAXFC"): s += 5
        if r.cat == "JUD": s += 8; flags.append("JUDGMENT")
        if r.cat == "LIEN": s += 7; flags.append("LIEN")
        if r.cat == "PRO": s += 12; flags.append("PROBATE")
        if r.amount > 100000: s += 15; flags.append("HIGH_AMOUNT")
        elif r.amount > 50000: s += 10; flags.append("MID_AMOUNT")
        if r.filed:
            try:
                if datetime.strptime(r.filed, "%Y-%m-%d") >= start:
                    s += 5; flags.append("NEW_THIS_WEEK")
            except ValueError:
                pass
        if r.prop_address:
            s += 5; flags.append("HAS_ADDRESS")
        r.score = min(s, 100)
        r.flags = flags

# ---------------------------------------------------------------------------
# Outputs (dashboard data contract -- identical to Bexar)
# ---------------------------------------------------------------------------
DASH_CAT = {
    "LP": "foreclosure", "FC": "foreclosure", "TAXFC": "foreclosure",
    "TAXDEED": "tax_lien", "LIEN": "tax_lien",
    "JUD": "judgment", "PRO": "probate",
}
FLAG_NICE = {
    "LIS_PENDENS": "Lis pendens", "FORECLOSURE": "Pre-foreclosure",
    "TAX_FORECLOSURE": "Tax foreclosure", "TAX_DEED": "Tax deed",
    "JUDGMENT": "Judgment lien", "LIEN": "Tax lien",
    "PROBATE": "Probate / estate", "HIGH_AMOUNT": "Amount > $100k",
    "MID_AMOUNT": "Amount > $50k", "NEW_THIS_WEEK": "New this week",
    "HAS_ADDRESS": "Has address",
}


def write_outputs(records: list, start: datetime, end: datetime) -> None:
    base = _repo_base()
    for d in [base / "dashboard", base / "data"]:
        d.mkdir(parents=True, exist_ok=True)
    week_ago = (end - timedelta(days=7)).strftime("%Y-%m-%d")
    recs_out = []
    for r in records:
        d = asdict(r)
        d.pop("parcel_id", None)
        d["cat_code"] = r.cat
        d["cat"] = DASH_CAT.get(r.cat, "tax_lien")
        d["flags"] = [FLAG_NICE.get(f, f) for f in (r.flags or [])]
        d["absentee"] = bool(
            r.prop_address and r.mail_address
            and r.prop_address.upper() != r.mail_address.upper())
        d["out_of_state"] = bool(r.mail_state and r.mail_state.upper() != STATE)
        recs_out.append(d)
    payload = {
        "fetched_at": datetime.utcnow().isoformat(),
        "county": COUNTY,
        "source": f"{COUNTY} County, {STATE} -- Clerk Official Records + "
                  "RealForeclose/RealTaxdeed Auctions + FL DOR Parcels",
        "date_range": {"start": start.strftime("%Y-%m-%d"), "end": end.strftime("%Y-%m-%d")},
        "total": len(records),
        "new_7d": sum(1 for r in records if (r.first_seen or "") >= week_ago),
        "with_address": sum(1 for r in records if r.prop_address),
        "by_cat": {c: sum(1 for r in records if r.cat == c) for c in ("FC","TAXFC","TAXDEED","LP","JUD","LIEN","PRO")},
        "records": recs_out,
    }
    for path in [base / "dashboard" / "records.json", base / "data" / "records.json"]:
        path.write_text(json.dumps(payload, indent=2, default=str))
        log.info("JSON written: %s (%d records)", path, len(records))
    csv_path = base / "data" / "ghl_export.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(GHL_HEADERS.values()))
        writer.writeheader()
        for r in records:
            d = asdict(r)
            writer.writerow({GHL_HEADERS[k]: ("|".join(d[k]) if k=="flags" else d[k]) for k in GHL_FIELDS})
    log.info("GHL CSV written: %s (%d records)", csv_path, len(records))
    skip_path = base / "data" / "skiptrace_export.csv"
    skip_cols = ["First Name", "Last Name", "Mailing Address", "Mailing City",
                 "Mailing State", "Mailing Zip", "Property Address",
                 "Property City", "Property State", "Property Zip"]
    with open(skip_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=skip_cols)
        writer.writeheader()
        for r in records:
            first, last = split_index_name(r.owner)
            writer.writerow({
                "First Name": first.title(), "Last Name": last.title() if first else last,
                "Mailing Address": r.mail_address, "Mailing City": r.mail_city,
                "Mailing State": r.mail_state, "Mailing Zip": r.mail_zip,
                "Property Address": r.prop_address, "Property City": r.prop_city,
                "Property State": r.prop_state, "Property Zip": r.prop_zip,
            })
    log.info("Skip trace CSV written: %s (%d records)", skip_path, len(records))

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main() -> None:
    parser = argparse.ArgumentParser(description="Polk County lead scraper")
    parser.add_argument("--days", type=int, default=LOOKBACK_DAYS)
    parser.add_argument("--probate-days", type=int, default=PROBATE_LOOKBACK_DAYS)
    parser.add_argument("--skip-parcel", action="store_true")
    parser.add_argument("--skip-auctions", action="store_true")
    args = parser.parse_args()
    end = datetime.now()
    start = end - timedelta(days=args.days)
    probate_start = end - timedelta(days=args.probate_days)
    log.info("=" * 60)
    log.info("Polk County Motivated Seller Lead Scraper")
    log.info("Lookback default=%dd  probate=%dd", args.days, args.probate_days)
    log.info("=" * 60)
    log.info("Range: default %s->%s | probate %s->%s",
             start.strftime("%m/%d/%Y"), end.strftime("%m/%d/%Y"),
             probate_start.strftime("%m/%d/%Y"), end.strftime("%m/%d/%Y"))
    scraper = ClerkScraper(start, end, probate_start)
    records = scraper.run()
    if not args.skip_auctions:
        auction_recs = (
            fetch_realauction(RF_BASE, "FC", "Foreclosure Auction", "FORECLOSURE SALE")
            + fetch_realauction(RTD_BASE, "TAXDEED", "Tax Deed Auction", "TAX DEED SALE"))
        existing_ids = {r.doc_num for r in records if r.doc_num}
        existing_addr = {r.prop_address.upper() for r in records if r.prop_address}
        for r in auction_recs:
            if r.doc_num and r.doc_num in existing_ids:
                continue
            if r.prop_address and r.prop_address.upper() in existing_addr:
                continue
            records.append(r)
            if r.doc_num:
                existing_ids.add(r.doc_num)
            if r.prop_address:
                existing_addr.add(r.prop_address.upper())
    if not args.skip_parcel:
        enrich_parcels(records)
    detect_changes(records)
    score_records(records, start)
    records.sort(key=lambda r: (r.status != "NEW", -r.score))
    if not records:
        log.warning("No records found. Writing empty output files.")
    else:
        log.info("Total after dedup + enrichment: %d", len(records))
    write_outputs(records, start, end)
    pro_count = sum(1 for r in records if r.cat == "PRO")
    pro_with_addr = sum(1 for r in records if r.cat == "PRO" and r.prop_address)
    log.info("=" * 60)
    log.info("SUMMARY")
    log.info("  Total records  : %d", len(records))
    log.info("  With address   : %d", sum(1 for r in records if r.prop_address))
    log.info("  Probates       : %d (%d with address)", pro_count, pro_with_addr)
    log.info("  Score >= 70    : %d", sum(1 for r in records if r.score >= 70))
    log.info("  Score >= 50    : %d", sum(1 for r in records if r.score >= 50))


if __name__ == "__main__":
    main()

from __future__ import annotations

import argparse
import base64
import csv
import hashlib
import json
import logging
import os
import re
import sys
import time
from datetime import datetime, timedelta
from urllib.parse import urljoin, urlparse
from urllib.robotparser import RobotFileParser

import requests
from requests.adapters import HTTPAdapter

try:
    from urllib3.util.retry import Retry
except Exception:
    Retry = None

from bs4 import BeautifulSoup

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    datefmt="%H:%M:%S",
)
logger = logging.getLogger("jobscraper")

# ── Output columns ─────────────────────────────────────────────────────────────
APPSCRIPT_COLUMNS = [
    "Job Title", "Job Type", "Job Qualifications", "Job Experience",
    "Job Location", "Job Field", "Date Posted", "Deadline",
    "Job Description", "Application", "Company URL", "Company Name",
    "Company Logo", "Company Industry", "Company Founded", "Company Type",
    "Company Website", "Company Address", "Company Details", "Job URL",
    "Estimated Deadline", "Salary Range",
]

# ── Normalised job-type vocabulary ─────────────────────────────────────────────
JOB_TYPE_MAPPING = {
    "full-time": "full-time", "full time": "full-time", "fulltime": "full-time",
    "permanent": "full-time",
    "part-time": "part-time", "part time": "part-time", "parttime": "part-time",
    "contract": "contract", "contractor": "contract", "contracting": "contract",
    "fixed-term": "contract", "fixed term": "contract",
    "temporary": "temporary", "temp": "temporary", "seasonal": "temporary",
    "freelance": "freelance",
    "internship": "internship", "intern": "internship", "graduate": "internship",
    "volunteer": "volunteer",
}

# ── Politeness / safety knobs ──────────────────────────────────────────────────
REQUEST_DELAY_SECONDS = 2.0
REQUEST_TIMEOUT       = 20
MAX_RETRIES           = 3
USER_AGENT = (
    "DataAxisNodeJobBot/1.0 (+https://dataaxisnode.com; aggregator; "
    "contact admin@dataaxisnode.com)"
)
RESPECT_ROBOTS = True

DEFAULT_DEADLINE_DAYS = 30

MISTRAL_MODEL = "mistral-small-latest"
MISTRAL_URL   = "https://api.mistral.ai/v1/chat/completions"

COUNTRY_KEY      = "cambodia"
COUNTRY_NAME     = "Cambodia"
DEFAULT_LOCATION = "Cambodia"

TRACKER_FILE = "processed_cambodia.csv"
OUTPUT_CSV   = "scraped_cambodia.csv"

SOURCE_REGISTRY: dict[str, type] = {}
DEFAULT_LIMIT = 10


# ════════════════════════════════════════════════════════════════════════════════
# Secrets
# ════════════════════════════════════════════════════════════════════════════════
def get_secret(name: str, default: str | None = None, required: bool = False) -> str:
    val = os.environ.get(name, default)
    if required and not val:
        raise RuntimeError(
            f"Missing required secret: {name}. "
            "Add it under Settings -> Secrets -> Actions (or export it locally)."
        )
    return val or ""


# ════════════════════════════════════════════════════════════════════════════════
# Polite HTTP client
# ════════════════════════════════════════════════════════════════════════════════
class HttpClient:
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
        })
        if Retry is not None:
            retry = Retry(
                total=MAX_RETRIES, backoff_factor=1.0,
                status_forcelist=(429, 500, 502, 503, 504),
                allowed_methods=frozenset(["GET", "HEAD"]),
            )
            adapter = HTTPAdapter(max_retries=retry)
            self.session.mount("https://", adapter)
            self.session.mount("http://", adapter)
        self._last_hit: dict[str, float] = {}
        self._robots: dict[str, RobotFileParser | None] = {}

    def _allowed(self, url: str) -> bool:
        if not RESPECT_ROBOTS:
            return True
        parsed = urlparse(url)
        host = f"{parsed.scheme}://{parsed.netloc}"
        if host not in self._robots:
            rp = None
            try:
                resp = self.session.get(f"{host}/robots.txt", timeout=10)
                if resp.status_code == 200 and resp.text.strip():
                    rp = RobotFileParser()
                    rp.parse(resp.text.splitlines())
            except Exception:
                rp = None
            self._robots[host] = rp
        rp = self._robots[host]
        if rp is None:
            return True
        try:
            return rp.can_fetch(USER_AGENT, url)
        except Exception:
            return True

    def _throttle(self, url: str):
        host = urlparse(url).netloc
        last = self._last_hit.get(host, 0.0)
        wait = REQUEST_DELAY_SECONDS - (time.time() - last)
        if wait > 0:
            logger.debug("Throttling %.1fs for %s", wait, host)
            time.sleep(wait)
        self._last_hit[host] = time.time()

    def get(self, url: str, timeout: int | None = None,
            extra_headers: dict | None = None):
        if not self._allowed(url):
            logger.warning("robots.txt disallows %s — skipping", url)
            return None
        self._throttle(url)
        try:
            merged_headers = {}
            if extra_headers:
                merged_headers.update(extra_headers)
            r = self.session.get(url, timeout=timeout or REQUEST_TIMEOUT,
                                 headers=merged_headers)
            r.raise_for_status()
            r.encoding = r.apparent_encoding or "utf-8"
            logger.debug("GET %s  [%d]", url, r.status_code)
            return r
        except Exception as e:
            logger.warning("GET failed %s — %s", url, e)
            return None

    def get_text(self, url: str, timeout: int | None = None,
                 extra_headers: dict | None = None) -> str:
        r = self.get(url, timeout=timeout, extra_headers=extra_headers)
        return r.text if r is not None else ""

    def get_json(self, url: str, timeout: int | None = None,
                 extra_headers: dict | None = None):
        r = self.get(url, timeout=timeout, extra_headers=extra_headers)
        if r is None:
            return None
        try:
            return r.json()
        except Exception as e:
            logger.warning("JSON decode failed for %s — %s", url, e)
            return None


# ════════════════════════════════════════════════════════════════════════════════
# Text cleaning
# ════════════════════════════════════════════════════════════════════════════════
_MOJIBAKE = [
    ("\u00e2\u20ac\u2122", "'"), ("\u00e2\u20ac\u0153", '"'), ("\u00e2\u20ac\x9d", '"'),
    ("\u00e2\u20ac\u201c", "\u2013"), ("\u00e2\u20ac\u201d", "\u2014"),
    ("\u00e2\u20ac\u00a2", "\u2022"), ("\u00e2\u201e\u00a2", "\u2122"),
    ("\u00c2", ""), ("\u00e2\u20ac", '"'),
    ("\u00a0", " "), ("\u200b", ""), ("\ufeff", ""), ("&amp;", "&"),
    ("&#160;", " "), ("&nbsp;", " "),
]


def fix_mojibake(text: str) -> str:
    for a, b in _MOJIBAKE:
        text = text.replace(a, b)
    return re.sub(r"[\x00-\x08\x0B\x0C\x0E-\x1F\x7F]", "", text)


def sanitize_text(text, is_url: bool = False, is_email: bool = False) -> str:
    if text is None:
        return ""
    text = str(text).strip()
    if text.lower() in ("nan", "none", "n/a", "na", ""):
        return ""
    text = fix_mojibake(text)
    if is_url or is_email:
        return re.sub(r"\s+", " ", text).strip()
    text = re.sub(r"#+\s*", "", text)
    text = re.sub(r"\*\*", "", text)
    text = re.sub(r"[^\x20-\x7E\n\u00C0-\u017F\u2013\u2014\u2018-\u201D\u2022]", "", text)
    text = re.sub(r"[ \t]+", " ", text)
    return re.sub(r"\n{3,}", "\n\n", text).strip()


# ════════════════════════════════════════════════════════════════════════════════
# Description cleaning
# ════════════════════════════════════════════════════════════════════════════════
_NOISE_LINE_RE = re.compile(
    r"""(?:
        it\s+appears\s+(you|that)\b |
        could\s+you\s+please\s+(share|provide) |
        please\s+provide\s+the\s+(full|original|complete)\s+ |
        i['']d\s+be\s+happy\s+to\s+assist |
        i\s+(don['']t\s+have|am\s+unable) |
        since\s+i\s+don['']t\s+have |
        here['']?s?\s+(a\s+)?professional\s+(version|rewrite|paragraph) |
        rewritten?\s+version\s*: |
        rephrased\s+version\s*: |
        output\s+only\s+the\s+rewritten |
        rewrite\s+this\s+job\s+(description|title) |
        preserve\s+all\s+(original\s+)?facts |
        use\s+different\s+(sentence\s+structure|vocabulary|wording) |
        ^(paragraph|version|revised|professional\s+version)\s*:?\s*$ |
        ^note\s*:?\s*$ |
        ^we\s+ensure\s+you\s+remain\s+informed\s+of\s+every\s+new\s+job |
        ^we\s+encourage\s+you\s+to\s+register\s+for\s+updates |
        select\s+the\s+subscription\s+option |
        register\s+for\s+updates\s+and\s+notifications |
        ^follow\s*$ | ^browse\s+by\s*$ | ^date\s+posted\s*$ |
        ^(today|this\s+week|last\s+week|this\s+month)\s*$ |
        ^latest\s+jobs\s+posted\s*$ |
        ^hot\s*$ | ^or\s*$ |
        ^name\s*\*?\s*$ | ^message\s*\*?\s*$ |
        ^\(note:\s
    )""",
    re.I | re.X | re.MULTILINE,
)

_BOILERPLATE_CUTOFF_RE = re.compile(
    r"""(?:
        we\s+invite\s+you\s+to\s+submit\s+your\s+application\s+for\s+this\s+exciting\s+opportunity |
        please\s+submit\s+your\s+curr?iculum\s+vitae |
        the\s+application\s+deadline\s+for\s+submissions |
        professional\s+career\s+development\s+services\b |
        we\s+ensure\s+you\s+remain\s+informed\s+of\s+every\s+new\s+job\s+opportunity |
        we\s+encourage\s+you\s+to\s+register\s+for\s+updates\s+and\s+notifications
    )""",
    re.I | re.X | re.DOTALL,
)

_BRACKET_RE = re.compile(r"\[[^\]]{1,80}\]")
_TINY_BRACKET_LINE_RE = re.compile(r"^\s*\[[^\]]{1,15}\]\s*[.,]?\s*$")


def _should_drop_placeholder_line(line: str) -> bool:
    if not _BRACKET_RE.search(line):
        return False
    if _TINY_BRACKET_LINE_RE.match(line):
        return True
    bracket_text = " ".join(_BRACKET_RE.findall(line))
    bracket_words = len(bracket_text.split())
    total_words   = len(line.split())
    real_words    = total_words - bracket_words
    return real_words < 3


def clean_description(text: str) -> str:
    if not text:
        return ""
    text = fix_mojibake(text)
    clean_lines: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            clean_lines.append("")
            continue
        if _NOISE_LINE_RE.search(stripped):
            continue
        if _should_drop_placeholder_line(stripped):
            continue
        clean_lines.append(line)
    text = "\n".join(clean_lines)
    m = _BOILERPLATE_CUTOFF_RE.search(text)
    if m:
        text = text[:m.start()].strip()
    text = re.sub(r"\n{3,}", "\n\n", text)
    paras = [p.strip() for p in text.split("\n\n")]
    paras = [p for p in paras if p and len(p.split()) >= 4]
    return "\n\n".join(paras).strip()


# ════════════════════════════════════════════════════════════════════════════════
# Date parsing
# ════════════════════════════════════════════════════════════════════════════════
_MONTHS = {m.lower(): i for i, m in enumerate(
    ["", "January", "February", "March", "April", "May", "June", "July",
     "August", "September", "October", "November", "December"]) if m}
_MONTHS.update({m[:3]: i for m, i in list(_MONTHS.items())})


def parse_date(raw: str, fallback_today: bool = False) -> str:
    raw = sanitize_text(raw)
    if not raw:
        return datetime.now().strftime("%Y-%m-%d") if fallback_today else ""
    raw = re.sub(r"(?i)\b(posted|apply by|closing date|deadline|on)\b[:\s]*", "", raw).strip()
    raw = re.sub(r"(\d+)(st|nd|rd|th)", r"\1", raw, flags=re.I)
    for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%m/%d/%Y", "%d.%m.%Y",
                "%d/%b/%Y", "%d-%b-%Y", "%d %b %Y", "%d %B %Y"):
        try:
            return datetime.strptime(raw[:11].strip(), fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    m = re.search(r"(\d{1,2})\s+([A-Za-z]+)\s*(\d{4})?", raw)
    if m and m.group(2).lower()[:3] in _MONTHS:
        d, mon, y = int(m.group(1)), _MONTHS[m.group(2).lower()[:3]], m.group(3)
        y = int(y) if y else datetime.now().year
        try:
            return datetime(y, mon, d).strftime("%Y-%m-%d")
        except ValueError:
            pass
    m = re.search(r"([A-Za-z]+)\s+(\d{1,2}),?\s*(\d{4})?", raw)
    if m and m.group(1).lower()[:3] in _MONTHS:
        mon, d, y = _MONTHS[m.group(1).lower()[:3]], int(m.group(2)), m.group(3)
        y = int(y) if y else datetime.now().year
        try:
            return datetime(y, mon, d).strftime("%Y-%m-%d")
        except ValueError:
            pass
    return datetime.now().strftime("%Y-%m-%d") if fallback_today else ""


def estimated_deadline(date_posted: str, deadline: str) -> str:
    if deadline:
        return deadline
    base = parse_date(date_posted, fallback_today=True)
    try:
        dt = datetime.strptime(base, "%Y-%m-%d") + timedelta(days=DEFAULT_DEADLINE_DAYS)
        return dt.strftime("%Y-%m-%d")
    except ValueError:
        return ""


def make_job_id(job_url: str, title: str = "", company: str = "") -> str:
    src  = sanitize_text(job_url, is_url=True)
    seed = src if src else f"{title}|{company}"
    return hashlib.md5(seed.encode("utf-8")).hexdigest()[:16]


# ── Cross-source content fingerprint ──────────────────────────────────────────
_FP_NOISE_RE = re.compile(
    r"\b(job|jobs|vacanc(?:y|ies)|position|opening|career|opportunit(?:y|ies)|"
    r"urgent(?:ly)?|hiring|wanted|needed|new|latest|apply\s*now|full\s*time|"
    r"part\s*time|x\d+|\(\d+\)|grade\s*\w+|in\s+(?:phnom\s*penh|siem\s*reap|"
    r"sihanoukville|battambang|kampong\s*cham|cambodia))\b",
    re.I,
)
_FP_COMPANY_SUFFIX_RE = re.compile(
    r"\b(plc|ltd|limited|inc|incorporated|corp|corporation|co|company|"
    r"group|holdings|cambodia|co\.?\s*ltd)\b\.?",
    re.I,
)
_FP_PUNCT_RE = re.compile(r"[^a-z0-9 ]+")


def _fp_normalise(text: str) -> str:
    text = sanitize_text(text).lower()
    text = _FP_PUNCT_RE.sub(" ", text)
    text = _FP_NOISE_RE.sub(" ", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def _fp_normalise_company(text: str) -> str:
    text = _fp_normalise(text)
    text = _FP_COMPANY_SUFFIX_RE.sub(" ", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def make_fingerprint(title: str, company: str) -> str:
    norm_title   = _fp_normalise(title)
    norm_company = _fp_normalise_company(company)
    seed = f"{norm_title}|{norm_company}"
    return hashlib.md5(seed.encode("utf-8")).hexdigest()[:16]


def fingerprint_similarity(title_a: str, company_a: str,
                           title_b: str, company_b: str) -> float:
    t_sim = _similarity(_fp_normalise(title_a), _fp_normalise(title_b))
    c_a, c_b = _fp_normalise_company(company_a), _fp_normalise_company(company_b)
    if c_a and c_b:
        c_sim = _similarity(c_a, c_b)
    else:
        c_sim = t_sim
    return (t_sim * 0.75) + (c_sim * 0.25)


def normalise_job_type(raw: str) -> str:
    raw = sanitize_text(raw).lower()
    for key, val in JOB_TYPE_MAPPING.items():
        if key in raw:
            return val
    return "full-time"


def domain_of(url: str) -> str:
    try:
        return urlparse(url).netloc.lower().replace("www.", "")
    except Exception:
        return ""


# ════════════════════════════════════════════════════════════════════════════════
# Application-route extraction
# ════════════════════════════════════════════════════════════════════════════════
EMAIL_RE = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
APPLY_CTX = re.compile(
    r"(how to apply|method of application|to apply|apply (?:now|here|online|via|through|by)|"
    r"send (?:your )?(?:cv|resume|application)|submit (?:your )?(?:cv|application)|"
    r"forward (?:your )?(?:cv|application)|email (?:your )?(?:cv|application))",
    re.I,
)
EMAIL_BLOCKLIST = re.compile(
    r"(noreply|no-reply|donotreply|webmaster|privacy|unsubscribe|example\.|sentry|"
    r"wordpress|wixpress|sentry\.io|@2x|\.png|\.jpg|\.svg)",
    re.I,
)


def _visible_text(soup: BeautifulSoup) -> str:
    for tag in soup(["script", "style", "noscript"]):
        tag.decompose()
    return soup.get_text("\n", strip=True)


def extract_application(html: str, page_url: str) -> str:
    soup = BeautifulSoup(html, "html.parser")
    site_domain = domain_of(page_url)
    text = _visible_text(soup)

    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if href.lower().startswith("mailto:"):
            email = href.split(":", 1)[1].split("?")[0].strip()
            if email and not EMAIL_BLOCKLIST.search(email):
                return sanitize_text(email, is_email=True)

    for a in soup.find_all("a", href=True):
        label = (a.get_text(" ", strip=True) or "").lower()
        href = urljoin(page_url, a["href"].strip())
        if not href.lower().startswith("http"):
            continue
        if re.search(r"\bapply\b|application", label) or re.search(r"\bapply\b", href.lower()):
            d = domain_of(href)
            if d and d != site_domain and "linkedin" not in d:
                return sanitize_text(href, is_url=True)

    cue = APPLY_CTX.search(text)
    if cue:
        tail = text[cue.start():cue.start() + 800]
        for em in EMAIL_RE.findall(tail):
            if not EMAIL_BLOCKLIST.search(em) and domain_of("http://" + em.split("@")[1]) != site_domain:
                return sanitize_text(em, is_email=True)

    for em in EMAIL_RE.findall(text):
        if not EMAIL_BLOCKLIST.search(em) and em.split("@")[1].lower() not in (site_domain,):
            return sanitize_text(em, is_email=True)

    return ""


def extract_application_from_text(text: str, page_domain: str = "") -> str:
    """Mine an email or external apply URL from plain text."""
    cue = APPLY_CTX.search(text)
    if cue:
        tail = text[cue.start():cue.start() + 800]
        for em in EMAIL_RE.findall(tail):
            if not EMAIL_BLOCKLIST.search(em):
                dom = em.split("@")[1].lower()
                if dom != page_domain:
                    return sanitize_text(em, is_email=True)
    for em in EMAIL_RE.findall(text):
        if not EMAIL_BLOCKLIST.search(em):
            dom = em.split("@")[1].lower()
            if dom != page_domain:
                return sanitize_text(em, is_email=True)
    for m in re.finditer(r"https?://\S+", text):
        href = m.group(0).rstrip(".,)")
        if re.search(r"\bapply\b", href, re.I) and "camhr.com" not in href:
            return sanitize_text(href, is_url=True)
    return ""


def has_application(record: dict) -> bool:
    app = sanitize_text(record.get("Application", ""))
    if not app:
        return False
    is_email = bool(re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", app))
    is_url   = app.lower().startswith("http")
    return is_email or is_url


# ════════════════════════════════════════════════════════════════════════════════
# Company-website enrichment
# ════════════════════════════════════════════════════════════════════════════════
COMPANY_FIELDS = [
    "Company Website", "Company Logo", "Company Details", "Company Industry",
    "Company Founded", "Company Address", "Company Type",
]
_FOUNDED_RE = re.compile(
    r"(?:founded|established|incorporated|since|operating since)\s*(?:in\s*)?(\d{4})", re.I)


class CompanyEnricher:
    def __init__(self, http: HttpClient):
        self.http = http
        self._cache: dict[str, dict] = {}

    def enrich(self, record: dict) -> dict:
        site = sanitize_text(record.get("Company Website", ""), is_url=True)
        if not site:
            site = self._guess_site(record)
        if not site or not site.startswith("http"):
            return record
        data = self._cache.get(site) or self._scrape_site(site)
        self._cache[site] = data
        if not record.get("Company Website"):
            record["Company Website"] = site
        for field, key in [
            ("Company Details", "details"), ("Company Logo", "logo"),
            ("Company Industry", "industry"), ("Company Founded", "founded"),
            ("Company Address", "address"), ("Company URL", "url"),
        ]:
            if not sanitize_text(record.get(field, "")) and data.get(key):
                record[field] = data[key]
        if not has_application(record) and data.get("email"):
            record["Application"] = data["email"]
        return record

    def _guess_site(self, record: dict) -> str:
        app = sanitize_text(record.get("Application", ""))
        if "@" in app and not app.startswith("http"):
            dom = app.split("@")[1].strip()
            free = ("gmail.", "yahoo.", "hotmail.", "outlook.", "live.", "icloud.")
            if dom and not any(dom.startswith(f) or f in dom for f in free):
                return f"https://{dom}"
        return ""

    def _scrape_site(self, site: str) -> dict:
        out: dict = {"url": site, "website": site}
        html = self.http.get_text(site)
        if not html:
            host = urlparse(site).netloc
            html = self.http.get_text(f"https://{host}") if host else ""
        if not html:
            return out
        soup = BeautifulSoup(html, "html.parser")
        self._from_jsonld(soup, out)
        self._from_meta(soup, site, out)
        if len(out.get("details", "")) < 60:
            about = self._find_internal(soup, site, ("about", "who-we-are", "company"))
            if about:
                ahtml = self.http.get_text(about)
                if ahtml:
                    asoup = BeautifulSoup(ahtml, "html.parser")
                    self._from_jsonld(asoup, out)
                    para = self._first_paragraph(asoup)
                    if para and len(para) > len(out.get("details", "")):
                        out["details"] = para
                    out.setdefault("founded", self._founded(asoup.get_text(" ", strip=True)))
        if not out.get("email"):
            contact = self._find_internal(soup, site, ("contact", "careers", "vacancies"))
            chtml = self.http.get_text(contact) if contact else ""
            blob = chtml or html
            m = EMAIL_RE.search(blob)
            if m and not EMAIL_BLOCKLIST.search(m.group(0)):
                out["email"] = sanitize_text(m.group(0), is_email=True)
        out["founded"] = out.get("founded") or self._founded(soup.get_text(" ", strip=True))
        return {k: v for k, v in out.items() if v}

    def _from_jsonld(self, soup, out):
        for tag in soup.find_all("script", type="application/ld+json"):
            try:
                data = json.loads(tag.string or "{}")
            except Exception:
                continue
            for node in (data if isinstance(data, list) else [data]):
                if not isinstance(node, dict):
                    continue
                t = str(node.get("@type", "")).lower()
                if "organization" in t or "localbusiness" in t or "corporation" in t:
                    out.setdefault("details", sanitize_text(node.get("description", "")))
                    logo = node.get("logo")
                    if isinstance(logo, dict):
                        logo = logo.get("url")
                    out.setdefault("logo", sanitize_text(logo or "", is_url=True))
                    out.setdefault("url", sanitize_text(node.get("url", ""), is_url=True))
                    fd = node.get("foundingDate", "")
                    if fd:
                        out.setdefault("founded", str(fd)[:4])
                    addr = node.get("address")
                    if isinstance(addr, dict):
                        parts = [addr.get(k, "") for k in
                                 ("streetAddress", "addressLocality", "addressRegion",
                                  "postalCode", "addressCountry")]
                        out.setdefault("address", sanitize_text(", ".join(p for p in parts if p)))
                    elif isinstance(addr, str):
                        out.setdefault("address", sanitize_text(addr))
                    ind = node.get("industry") or node.get("knowsAbout")
                    if ind:
                        out.setdefault("industry", sanitize_text(
                            ind if isinstance(ind, str) else ", ".join(ind)))

    def _from_meta(self, soup, site, out):
        if not out.get("details"):
            for sel in [("meta", {"name": "description"}),
                        ("meta", {"property": "og:description"})]:
                tag = soup.find(*sel)
                if tag and tag.get("content"):
                    out["details"] = sanitize_text(tag["content"])
                    break
        if not out.get("logo"):
            og = soup.find("meta", {"property": "og:image"})
            if og and og.get("content"):
                out["logo"] = sanitize_text(urljoin(site, og["content"]), is_url=True)
            else:
                img = soup.find("img", src=re.compile(r"logo", re.I))
                if img and img.get("src"):
                    out["logo"] = sanitize_text(urljoin(site, img["src"]), is_url=True)

    def _first_paragraph(self, soup) -> str:
        for p in soup.find_all("p"):
            txt = sanitize_text(p.get_text(" ", strip=True))
            if len(txt) > 80:
                return txt
        return ""

    def _founded(self, text: str) -> str:
        m = _FOUNDED_RE.search(text or "")
        return m.group(1) if m else ""

    def _find_internal(self, soup, site, keywords) -> str:
        host = domain_of(site)
        for a in soup.find_all("a", href=True):
            href = urljoin(site, a["href"])
            label = (a.get_text(" ", strip=True) or "").lower()
            if domain_of(href) != host:
                continue
            if any(k in href.lower() or k in label for k in keywords):
                return href
        return ""


# ════════════════════════════════════════════════════════════════════════════════
# Mistral paraphraser
# ════════════════════════════════════════════════════════════════════════════════
_st_model = None
try:
    import os as _os
    _os.environ.setdefault("TOKENIZERS_PARALLELISM", "false")
    from sentence_transformers import SentenceTransformer, util as _st_util
    try:
        from tqdm import tqdm as _tqdm
        import functools, tqdm as _tqdm_mod
        _tqdm_mod.tqdm = functools.partial(_tqdm_mod.tqdm, disable=True)
    except Exception:
        pass
    _st_model = SentenceTransformer("all-MiniLM-L6-v2", device="cpu")
    logger.info("sentence-transformers loaded for similarity scoring")
except Exception:
    import difflib
    logger.info("sentence-transformers not available — using difflib similarity")

_grammar = None
try:
    import language_tool_python
    _grammar = language_tool_python.LanguageTool(
        "en-US", remote_server="https://api.languagetool.org")
except Exception:
    _grammar = None


def _similarity(a: str, b: str) -> float:
    if not a or not b:
        return 0.0
    if _st_model is not None:
        try:
            emb = _st_model.encode([a, b], convert_to_tensor=True)
            return float(_st_util.pytorch_cos_sim(emb[0], emb[1]))
        except Exception:
            pass
    import difflib
    return difflib.SequenceMatcher(None, a.lower(), b.lower()).ratio()


def _grammar_correct(text: str) -> str:
    if not _grammar:
        return text
    try:
        return language_tool_python.utils.correct(text, _grammar.check(text))
    except Exception:
        return text


def _clean_para(text: str) -> str:
    text = fix_mojibake(text or "")
    for pat in [r"\[/?INST\]", r"</?s>",
                r"(?i)(rewritten?|rephrased?|output|paraphrase[d]?)[:\s]+",
                r"\*\*", r"###", r"---"]:
        text = re.sub(pat, "", text)
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return _grammar_correct(text.strip())


class Paraphraser:
    def __init__(self):
        self.api_key  = get_secret("MISTRAL_API_KEY")
        self.enabled  = bool(self.api_key)
        self._auth_bad = False
        if not self.enabled:
            logger.warning("MISTRAL_API_KEY not set — paraphrasing disabled (passthrough)")

    def _generate(self, prompt: str, max_tokens: int = 400, temperature: float = 0.7) -> str:
        if not self.enabled or self._auth_bad:
            return ""
        try:
            r = requests.post(
                MISTRAL_URL,
                headers={"Authorization": f"Bearer {self.api_key}",
                         "Content-Type": "application/json"},
                json={"model": MISTRAL_MODEL,
                      "messages": [{"role": "user", "content": prompt}],
                      "max_tokens": max_tokens, "temperature": temperature},
                timeout=30,
            )
            if r.status_code in (401, 403):
                logger.error("Mistral auth failed (%d) — disabling paraphrasing.", r.status_code)
                self._auth_bad = True
                self.enabled   = False
                return ""
            r.raise_for_status()
            return r.json()["choices"][0]["message"]["content"].strip()
        except requests.exceptions.HTTPError:
            return ""
        except Exception as e:
            logger.error("Mistral error: %s", e)
            return ""

    def title(self, title: str) -> str:
        clean = sanitize_text(title)
        if not clean or not self.enabled:
            return clean
        MAX_ATTEMPTS = 4
        print(f"\n ┌─ TITLE PARAPHRASE {'─'*45}")
        print(f" │ Original : \"{clean}\"")
        print(f" │ {'─'*64}")
        best, best_sim = None, 0.0
        for attempt in range(MAX_ATTEMPTS):
            if not self.enabled:
                break
            temp = round(0.68 + attempt * 0.06, 2)
            prompt = ("Rewrite this job title professionally using different words. "
                      "Output ONLY the rewritten title. Keep it 4-12 words.\n\n"
                      f"Job title: {clean}")
            res = _clean_para(self._generate(prompt, 50, temp)).split("\n")[0].strip().strip('"\'')
            wc  = len(res.split())
            sim = _similarity(clean, res) if res else 0.0
            dup = res.lower() == clean.lower()
            print(f" │ Attempt {attempt+1} (temp={temp}):")
            print(f" │    Output  : \"{res}\"" if res else " │    Output  : (empty)")
            print(f" │    Words   : {wc} | Similarity: {sim:.3f} | Dup: {'Yes' if dup else 'No'}")
            ok = res and 4 <= wc <= 14 and sim >= 0.55 and not dup
            if ok:
                print(f" │    → ✅ ACCEPTED (sim={sim:.3f})")
                if sim > best_sim:
                    best, best_sim = res, sim
                break
            else:
                reasons = []
                if not res:    reasons.append("empty")
                if wc < 4:     reasons.append(f"short ({wc}w)")
                if wc > 14:    reasons.append(f"long ({wc}w)")
                if sim < 0.55: reasons.append(f"sim={sim:.3f}")
                if dup:        reasons.append("dup")
                print(f" │    → ❌ REJECTED — {', '.join(reasons)}")
                if res and sim > best_sim:
                    best, best_sim = res, sim
            print(f" │ {'─'*64}")
            time.sleep(0.5)
        chosen = best or clean
        print(f" │ {'✅' if best else '⚠️ '} Final: \"{chosen}\"")
        print(f" └{'─'*65}\n")
        return chosen

    def description(self, text: str) -> str:
        clean = sanitize_text(text)
        if not clean or not self.enabled:
            return clean
        paras = [p.strip() for p in clean.split("\n") if p.strip()]
        print(f"\n ┌─ DESCRIPTION PARAPHRASE ({len(paras)} paragraphs) {'─'*25}")
        out = []
        for pi, para in enumerate(paras, 1):
            if not self.enabled:
                out.append(para)
                continue
            wc_orig = len(para.split())
            if wc_orig < 5:
                out.append(para)
                print(f" │ [Para {pi}/{len(paras)}] SKIPPED (too short)")
                continue
            print(f"\n │ ┌─ Paragraph {pi}/{len(paras)} {'─'*50}")
            accepted, best_res, best_sim = None, None, 0.0
            for attempt in range(3):
                if not self.enabled:
                    break
                temp = round(0.65 + attempt * 0.08, 2)
                prompt = ("Rewrite this job description paragraph professionally. "
                          "Keep ALL facts, requirements and responsibilities. "
                          "Use different sentence structure and vocabulary. "
                          "Output ONLY the rewritten paragraph.\n\n"
                          f"Original:\n{para}")
                res = _clean_para(self._generate(prompt, 500, temp))
                rw  = len(res.split()) if res else 0
                sim = _similarity(para, res) if rw >= 5 else 0.0
                print(f" │ │ Attempt {attempt+1}: words={rw} sim={sim:.3f}")
                if res and rw >= 8 and sim >= 0.48:
                    print(f" │ │ → ✅ ACCEPTED")
                    accepted = res
                    break
                else:
                    if res and sim > best_sim:
                        best_res, best_sim = res, sim
                    print(f" │ │ → ❌ rejected")
                time.sleep(0.5)
            chosen_para = accepted or (best_res if best_res and best_sim >= 0.40 else para)
            print(f" │ └{'─'*65}")
            out.append(chosen_para)
        print(f" └{'─'*65}\n")
        return "\n\n".join(out)

    def company(self, text: str) -> str:
        clean = sanitize_text(text)
        if not clean or not self.enabled:
            return clean
        prompt = ("Rewrite this company description professionally. Preserve all "
                  "facts. Use different wording. Output ONLY the rewritten text.\n\n"
                  f"Original:\n{clean}")
        res = _clean_para(self._generate(prompt, 600, 0.68))
        rw  = len(res.split()) if res else 0
        sim = _similarity(clean, res) if rw >= 10 else 0.0
        if res and rw >= 10 and sim >= 0.40:
            return res
        return clean


# ════════════════════════════════════════════════════════════════════════════════
# WordPress client
# ════════════════════════════════════════════════════════════════════════════════
class WordPressClient:
    def __init__(self):
        base = get_secret("WP_BASE_URL", required=True).rstrip("/")
        self.base        = base
        self.jobs_url    = f"{base}/job-listings"
        self.company_url = f"{base}/companies"
        self.media_url   = f"{base}/media"
        self.user        = get_secret("WP_USERNAME", required=True)
        self.app_pw      = get_secret("WP_APP_PASSWORD", required=True)
        self.verify      = get_secret("WP_VERIFY_SSL", "true").lower() != "false"
        if not self.verify:
            requests.packages.urllib3.disable_warnings()  # type: ignore

    def _headers(self):
        token = base64.b64encode(f"{self.user}:{self.app_pw}".encode()).decode()
        return {"Authorization": f"Basic {token}", "Content-Type": "application/json"}

    @staticmethod
    def _slug(name: str, limit: int = 80) -> str:
        return re.sub(r"[^a-z0-9-]", "-", name.lower().strip())[:limit].strip("-")

    def upload_logo(self, logo_url: str):
        logo_url = sanitize_text(logo_url, is_url=True)
        if not logo_url.startswith("http"):
            return None
        ext = logo_url.lower().rsplit(".", 1)[-1].split("?")[0]
        if ext not in ("png", "jpg", "jpeg", "webp", "gif", "svg"):
            ext = "jpg"
        try:
            img = requests.get(logo_url, timeout=15)
            img.raise_for_status()
            h = self._headers()
            fname = re.sub(r"[^a-zA-Z0-9._-]", "_",
                           logo_url.split("/")[-1].split("?")[0]) or f"logo.{ext}"
            h["Content-Disposition"] = f"attachment; filename={fname}"
            h["Content-Type"] = img.headers.get("content-type", "image/jpeg")
            r = requests.post(self.media_url, headers=h, data=img.content,
                              auth=(self.user, self.app_pw),
                              timeout=30, verify=self.verify)
            r.raise_for_status()
            return r.json().get("id")
        except Exception as e:
            logger.error("Logo upload failed (%s): %s", logo_url, e)
            return None

    def get_or_create_term(self, taxonomy_url: str, name: str):
        name = sanitize_text(name)
        if not name:
            return None
        slug = self._slug(name)
        try:
            r = requests.get(f"{taxonomy_url}?slug={slug}", headers=self._headers(),
                             timeout=10, verify=self.verify)
            terms = r.json()
            if isinstance(terms, list) and terms:
                return terms[0]["id"]
        except Exception:
            pass
        try:
            r = requests.post(taxonomy_url, json={"name": name, "slug": slug},
                              headers=self._headers(), auth=(self.user, self.app_pw),
                              timeout=10, verify=self.verify)
            return r.json().get("id")
        except Exception as e:
            logger.error("Term create '%s': %s", name, e)
            return None

    def save_company(self, rec: dict, details: str, tagline: str):
        name = sanitize_text(rec.get("Company Name", ""))
        if not name or name.lower() in ("unknown company", "nan"):
            return None, None
        slug = self._slug(name)
        try:
            r = requests.get(f"{self.company_url}?slug={slug}", headers=self._headers(),
                             timeout=10, verify=self.verify)
            posts = r.json()
            if isinstance(posts, list) and posts:
                logger.info("Company exists: %s", name)
                return posts[0]["id"], posts[0].get("link")
        except Exception:
            pass
        att = self.upload_logo(rec.get("Company Logo", ""))
        payload = {
            "title": name, "content": details or "", "status": "publish",
            "featured_media": att or 0,
            "meta": {
                "_company_name":     name,
                "_company_logo":     str(att) if att else "",
                "_company_industry": sanitize_text(rec.get("Company Industry", "")),
                "_company_website":  sanitize_text(rec.get("Company Website", ""), is_url=True),
                "_company_address":  sanitize_text(rec.get("Company Address", "")),
                "_company_founded":  sanitize_text(rec.get("Company Founded", "")),
                "_company_type":     sanitize_text(rec.get("Company Type", "")),
                "_company_tagline":  tagline,
            },
        }
        try:
            r = requests.post(self.company_url, json=payload, headers=self._headers(),
                              auth=(self.user, self.app_pw), timeout=20, verify=self.verify)
            r.raise_for_status()
            post = r.json()
            logger.info("Company posted: %s -> ID %s", name, post.get("id"))
            return post.get("id"), post.get("link")
        except Exception as e:
            logger.error("Company post '%s': %s", name, e)
            return None, None

    def save_job(self, rec: dict, title: str, description: str):
        h           = self._headers()
        location    = sanitize_text(rec.get("Job Location", "")) or DEFAULT_LOCATION
        job_type    = normalise_job_type(rec.get("Job Type", "Full-time"))
        application = sanitize_text(rec.get("Application", ""), is_url=True)
        deadline    = (sanitize_text(rec.get("Deadline", "")) or
                       sanitize_text(rec.get("Estimated Deadline", "")))
        is_email = bool(re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", application))
        is_url_v = bool(re.match(r"^https?://\S+$", application))
        if not (is_email or is_url_v):
            application = ""
        slug = self._slug(title)
        try:
            r = requests.get(f"{self.jobs_url}?slug={slug}", headers=h,
                             timeout=10, verify=self.verify)
            posts = r.json()
            if isinstance(posts, list) and posts:
                logger.info("Job already on WP: %s", title)
                return posts[0]["id"], posts[0].get("link")
        except Exception:
            pass
        att       = self.upload_logo(rec.get("Company Logo", ""))
        region_id = self.get_or_create_term(f"{self.base}/job_listing_region", location)
        type_id   = self.get_or_create_term(f"{self.base}/job_listing_type",
                                            job_type.replace("-", " ").title())
        payload = {
            "title": title, "content": description, "status": "publish",
            "featured_media": att or 0,
            "meta": {
                "_job_title":          title,
                "_job_location":       location,
                "_job_type":           job_type,
                "_job_description":    description,
                "_application":        application,
                "_job_expires":        deadline,
                "_company_name":       sanitize_text(rec.get("Company Name", "")),
                "_company_website":    sanitize_text(rec.get("Company Website", ""), is_url=True),
                "_company_logo":       str(att) if att else "",
                "_company_industry":   sanitize_text(rec.get("Company Industry", "")),
                "_company_address":    sanitize_text(rec.get("Company Address", "")),
                "_company_founded":    sanitize_text(rec.get("Company Founded", "")),
                "_company_type":       sanitize_text(rec.get("Company Type", "")),
                "_job_qualifications": sanitize_text(rec.get("Job Qualifications", "")),
                "_job_experiences":    sanitize_text(rec.get("Job Experience", "")),
                "_job_field":          sanitize_text(rec.get("Job Field", "")),
                "_job_source_url":     sanitize_text(rec.get("Job URL", ""), is_url=True),
                "_job_salary":         sanitize_text(rec.get("Salary Range", "")),
            },
        }
        if region_id:
            payload["job_listing_region"] = [region_id]
        if type_id:
            payload["job_listing_type"] = [type_id]
        for attempt in range(3):
            try:
                r = requests.post(self.jobs_url, json=payload, headers=h,
                                  auth=(self.user, self.app_pw),
                                  timeout=25, verify=self.verify)
                r.raise_for_status()
                post = r.json()
                logger.info("Job posted: '%s' -> WP ID %s", title, post.get("id"))
                return post.get("id"), post.get("link")
            except Exception as e:
                logger.error("Job post attempt %d failed: %s", attempt + 1, e)
                if attempt < 2:
                    time.sleep(2 ** attempt)
        return None, None


# ════════════════════════════════════════════════════════════════════════════════
# Dedupe + status tracker
# ════════════════════════════════════════════════════════════════════════════════
_TRACKER_COLUMNS = ["Job ID", "Source", "Job URL", "Job Title", "Company Name",
                    "Fingerprint", "Status", "Timestamp"]


def _tracker_init():
    if not os.path.exists(TRACKER_FILE):
        with open(TRACKER_FILE, "w", newline="", encoding="utf-8") as f:
            csv.writer(f).writerow(_TRACKER_COLUMNS)


def _tracker_rows() -> list[dict]:
    _tracker_init()
    with open(TRACKER_FILE, newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def _tracker_write(rows: list[dict]):
    with open(TRACKER_FILE, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=_TRACKER_COLUMNS)
        w.writeheader()
        for row in rows:
            w.writerow({c: row.get(c, "") for c in _TRACKER_COLUMNS})


def tracker_load() -> tuple[set, set]:
    rows = _tracker_rows()
    ids  = {(r.get("Job ID") or "") for r in rows}
    urls = {(r.get("Job URL") or "") for r in rows}
    return ids, urls


def tracker_load_fingerprints() -> tuple[set, list[dict]]:
    rows = _tracker_rows()
    exact_fps: set = set()
    fuzzy_index: list[dict] = []
    for r in rows:
        fp     = (r.get("Fingerprint") or "").strip()
        status = (r.get("Status") or "").split("|")[0]
        if not fp:
            continue
        exact_fps.add(fp)
        if status in ("read", "posted"):
            fuzzy_index.append({
                "fingerprint": fp,
                "title":       r.get("Job Title", ""),
                "company":     r.get("Company Name", ""),
                "source":      r.get("Source", ""),
            })
    return exact_fps, fuzzy_index


def _tracker_upsert(job_id: str, updates: dict):
    rows = _tracker_rows()
    for r in rows:
        if str(r.get("Job ID")) == str(job_id):
            r.update(updates)
            r["Timestamp"] = datetime.now().isoformat()
            _tracker_write(rows)
            return
    row = {c: "" for c in _TRACKER_COLUMNS}
    row.update({"Job ID": job_id, "Timestamp": datetime.now().isoformat()})
    row.update(updates)
    rows.append(row)
    _tracker_write(rows)


def tracker_mark_read(job_id, source, job_url, title, company, fingerprint=""):
    upd = {"Source": source, "Job URL": job_url, "Job Title": title,
           "Company Name": company, "Status": "read"}
    if fingerprint:
        upd["Fingerprint"] = fingerprint
    _tracker_upsert(job_id, upd)


def tracker_mark_posted(job_id, wp_id, wp_url):
    _tracker_upsert(job_id, {"Status": f"posted|wp_id={wp_id}|{wp_url}"})


def tracker_mark_failed(job_id, reason):
    _tracker_upsert(job_id, {"Status": f"failed|{str(reason)[:120]}"})


def tracker_summary():
    rows = _tracker_rows()
    if not rows:
        return
    counts: dict[str, int] = {}
    for r in rows:
        status = (r.get("Status") or "").split("|")[0] or "unknown"
        counts[status] = counts.get(status, 0) + 1
    icons = {"read": "*", "posted": "OK", "failed": "X"}
    print(f"\n{'='*48}\n TRACKER SUMMARY ({len(rows)} records)\n{'='*48}")
    for status, n in sorted(counts.items()):
        print(f" [{icons.get(status, '.')}] {status:<12} {n}")
    print("=" * 48 + "\n")


# ════════════════════════════════════════════════════════════════════════════════
# Field mining helpers
# ════════════════════════════════════════════════════════════════════════════════
def empty_record() -> dict:
    return {col: "" for col in APPSCRIPT_COLUMNS}


_LABELS = {
    "Job Type":           r"(?:job\s*type|employment\s*type|contract\s*type)",
    "Job Qualifications": r"(?:qualification|minimum\s*qualification|education|degree)s?",
    "Job Experience":     r"(?:experience(?:\s*(?:level|length))?|years?\s*of\s*experience)",
    "Job Location":       r"(?:location|job\s*location|city|province|region|town)",
    "Job Field":          r"(?:job\s*field|category|sector|industry|department)",
    "Salary Range":       r"(?:salary|remuneration|pay|compensation|wage)",
    "Deadline":           r"(?:deadline|closing\s*date|apply\s*by|expiry|close\s*date)",
    "Date Posted":        r"(?:date\s*posted|posted(?:\s*on)?|published|posted\s*date)",
    "Company Industry":   r"(?:company\s*industry|industry|business\s*type)",
}
_SALARY_RE = re.compile(
    r"((?:USD|KHR|US\$|\$|\u20ac|\u00a3)\s?[\d][\d,\. ]*\d"
    r"(?:\s?(?:-|to|\u2013)\s?(?:USD|KHR|US\$|\$|\u20ac|\u00a3)?\s?[\d][\d,\. ]*\d)?"
    r"(?:\s?(?:per|/)\s?(?:month|annum|year|hour|week))?)", re.I)


def mine_fields(text: str) -> dict:
    found = {}
    for field, label in _LABELS.items():
        m = re.search(rf"{label}\s*[:\-\u2013]\s*(.+)", text, re.I)
        if m:
            val = m.group(1).split("\n")[0].strip(" .;|")
            if 0 < len(val) < 160:
                found[field] = sanitize_text(val)
    if "Salary Range" not in found:
        ms = _SALARY_RE.search(text)
        if ms:
            found["Salary Range"] = sanitize_text(ms.group(1))
    return found


def _clean_title(raw: str) -> str:
    raw = sanitize_text(raw)
    raw = re.split(r"\s+[|\u2013-]\s+(?:CamHR|Cambodia Jobs|Phnom Penh Jobs)", raw)[0]
    raw = re.sub(r"\s*[-\u2013]\s*Apply by .*$", "", raw, flags=re.I)
    return raw.strip()


def _strip_html(html_fragment: str) -> str:
    if not html_fragment:
        return ""
    soup = BeautifulSoup(html_fragment, "html.parser")
    return soup.get_text("\n", strip=True)


# ════════════════════════════════════════════════════════════════════════════════
# SOURCE — CamHR  (https://www.camhr.com)
#
# CamHR is a Vue SPA. All data is loaded via JSON API calls the browser makes:
#
#   LIST   GET /a/job?page=N&param={"page":N,"size":15}
#          → { data: { records: [...], total, current, size } }
#
#   DETAIL GET /a/job/{id}
#          → { data: { ...full job object... } }
#
# The backend returns HTTP 500 to requests that don't include the
# browser-style Accept / Referer / Origin headers the SPA sends, so we
# supply them explicitly via extra_headers on every call.
#
# Application route priority:
#   1. email / contact_email directly on the job object
#   2. apply_url / application_url pointing off-site
#   3. company.email / company.contact_email
#   4. Mine the plain-text job description for an email or external URL
# ════════════════════════════════════════════════════════════════════════════════
class CamHRScraper:
    source_key = "camhr"
    base_url   = "https://www.camhr.com"

    _LIST_API   = "https://www.camhr.com/a/job"
    _DETAIL_API = "https://www.camhr.com/a/job/{job_id}"

    # These mimic what the browser SPA sends to its own backend.
    _API_HEADERS = {
        "Accept":           "application/json, text/plain, */*",
        "Referer":          "https://www.camhr.com/a/job",
        "Origin":           "https://www.camhr.com",
        "X-Requested-With": "XMLHttpRequest",
    }

    _PAGE_SIZE = 15
    _MAX_PAGES = 50

    def __init__(self, http: HttpClient):
        self.http             = http
        self.country          = COUNTRY_NAME
        self.default_location = DEFAULT_LOCATION

    # ── list page ─────────────────────────────────────────────────────────────
    def _fetch_list_page(self, page: int) -> list[dict]:
        param = json.dumps({"page": page, "size": self._PAGE_SIZE},
                           separators=(",", ":"))
        url = f"{self._LIST_API}?page={page}&param={param}"
        logger.info("[camhr] Fetching list page %d: %s", page, url)
        data = self.http.get_json(url, extra_headers=self._API_HEADERS)
        if not data:
            logger.warning("[camhr] No JSON on list page %d", page)
            return []
        # Shape: { "code": 0, "data": { "records": [...] } }
        #   or:  { "data": [...] }
        inner = data.get("data") or {}
        if isinstance(inner, list):
            return inner
        if isinstance(inner, dict):
            for key in ("records", "list", "jobs", "items", "data"):
                records = inner.get(key)
                if isinstance(records, list):
                    return records
        return []

    # ── detail ────────────────────────────────────────────────────────────────
    def _fetch_detail(self, job_id) -> dict:
        url  = self._DETAIL_API.format(job_id=job_id)
        data = self.http.get_json(url, extra_headers=self._API_HEADERS)
        if not data:
            return {}
        inner = data.get("data") or {}
        return inner if isinstance(inner, dict) else {}

    # ── record builder ────────────────────────────────────────────────────────
    def _build_record(self, list_job: dict, detail: dict, job_url: str) -> dict:
        j = {**list_job, **detail}   # detail fields override list fields

        title = _clean_title(
            sanitize_text(
                j.get("title") or j.get("name") or j.get("job_title") or ""
            )
        )

        # Company
        company_obj     = j.get("company") or {}
        company_name    = sanitize_text(company_obj.get("name") or j.get("company_name") or "")
        company_logo    = sanitize_text(
            company_obj.get("logo") or company_obj.get("logo_url") or
            j.get("company_logo") or "", is_url=True)
        if company_logo and not company_logo.startswith("http"):
            company_logo = f"{self.base_url}/{company_logo.lstrip('/')}"
        company_website = sanitize_text(
            company_obj.get("website") or j.get("company_website") or "", is_url=True)
        if company_website and not re.match(r"^https?://", company_website, re.I):
            company_website = f"https://{company_website}"
        company_details  = sanitize_text(
            _strip_html(company_obj.get("description") or j.get("company_description") or ""))
        company_industry = sanitize_text(
            company_obj.get("industry") or j.get("company_industry") or "")
        company_address  = sanitize_text(
            company_obj.get("address") or j.get("company_address") or
            j.get("location") or "")

        # Location
        location = sanitize_text(
            j.get("job_location") or j.get("city") or
            j.get("province") or j.get("district") or
            company_obj.get("address") or DEFAULT_LOCATION)

        # Job field / category
        cat_obj   = j.get("category") or j.get("job_category") or {}
        job_field = (
            sanitize_text(cat_obj.get("name") if isinstance(cat_obj, dict) else str(cat_obj))
            or sanitize_text(j.get("field") or j.get("job_field") or "")
        )

        # Job type
        job_type = sanitize_text(
            j.get("job_type") or j.get("employment_type") or j.get("type") or "")

        # Salary
        salary = self._format_salary(j)

        # Description
        description_html = (
            j.get("description") or j.get("job_description") or j.get("content") or "")
        description = _strip_html(description_html)

        # Dates — camhr often gives ISO timestamps; trim to YYYY-MM-DD
        date_posted = str(
            j.get("created_at") or j.get("posted_at") or
            j.get("publish_date") or j.get("post_date") or "")[:10]
        deadline = str(
            j.get("expired_at") or j.get("expiry_date") or
            j.get("deadline") or j.get("closing_date") or "")[:10]

        # Application
        application = self._extract_application(j, description)

        return {
            "Job Title":        title,
            "Company Name":     company_name,
            "Company Logo":     company_logo,
            "Company Website":  company_website,
            "Company Details":  company_details,
            "Company Industry": company_industry,
            "Company Address":  company_address,
            "Job Location":     location,
            "Job Field":        job_field,
            "Job Type":         job_type,
            "Job Description":  description,
            "Application":      application,
            "Salary Range":     salary,
            "Date Posted":      date_posted,
            "Deadline":         deadline,
        }

    @staticmethod
    def _extract_application(j: dict, description_text: str) -> str:
        # 1. Direct email on the job object
        for key in ("email", "contact_email", "apply_email", "application_email"):
            val = sanitize_text(j.get(key) or "")
            if val and re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", val):
                if not EMAIL_BLOCKLIST.search(val):
                    return sanitize_text(val, is_email=True)

        # 2. External apply URL
        for key in ("apply_url", "application_url", "apply_link", "external_url"):
            val = sanitize_text(j.get(key) or "", is_url=True)
            if val and val.lower().startswith("http") and "camhr.com" not in val.lower():
                return val

        # 3. Company-level email
        company_obj = j.get("company") or {}
        for key in ("email", "contact_email"):
            val = sanitize_text(company_obj.get(key) or "")
            if val and re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", val):
                if not EMAIL_BLOCKLIST.search(val):
                    return sanitize_text(val, is_email=True)

        # 4. Mine description text
        return extract_application_from_text(description_text, page_domain="camhr.com")

    @staticmethod
    def _format_salary(j: dict) -> str:
        min_s = j.get("min_salary") or j.get("salary_min") or j.get("salary_from")
        max_s = j.get("max_salary") or j.get("salary_max") or j.get("salary_to")
        if not min_s and not max_s:
            raw = j.get("salary") or j.get("salary_range") or j.get("compensation") or ""
            return sanitize_text(str(raw)) if raw else ""
        currency = sanitize_text(j.get("salary_currency") or j.get("currency") or "USD").upper()

        def fmt(v):
            try:
                f = float(v)
                return f"{int(f):,}" if f == int(f) else f"{f:,.2f}"
            except (TypeError, ValueError):
                return sanitize_text(str(v))

        if min_s and max_s and str(min_s) != str(max_s):
            salary = f"{currency} {fmt(min_s)} - {fmt(max_s)}"
        else:
            salary = f"{currency} {fmt(min_s or max_s)}"
        period = sanitize_text(j.get("salary_period") or j.get("pay_period") or "")
        if period:
            salary = f"{salary} / {period}"
        return sanitize_text(salary)

    # ── main scrape generator ─────────────────────────────────────────────────
    def run(self, max_jobs: int, processed_ids: set, processed_urls: set):
        quota_str = str(max_jobs) if max_jobs else "unlimited"
        logger.info(
            "─── [%s] Starting scrape from %s (quota: %s) ───",
            self.source_key.upper(), self._LIST_API, quota_str,
        )

        yielded      = 0
        page         = 1
        empty_streak = 0

        while True:
            if max_jobs and yielded >= max_jobs:
                break
            if page > self._MAX_PAGES:
                logger.warning("[camhr] Hit safety page cap (%d) — stopping", self._MAX_PAGES)
                break

            list_jobs = self._fetch_list_page(page)

            if not list_jobs:
                empty_streak += 1
                logger.info("[camhr] Page %d returned 0 jobs (streak=%d)", page, empty_streak)
                if empty_streak >= 2:
                    break
                page += 1
                continue
            empty_streak = 0

            new_on_page = 0
            for list_job in list_jobs:
                if max_jobs and yielded >= max_jobs:
                    break

                job_id = list_job.get("id") or list_job.get("job_id")
                slug   = list_job.get("slug") or list_job.get("url_slug") or ""
                if slug:
                    job_url = f"{self.base_url}/job/{slug}"
                elif job_id:
                    job_url = f"{self.base_url}/job/{job_id}"
                else:
                    logger.warning("[camhr] Job object has no id/slug — skipping")
                    continue

                job_url = sanitize_text(job_url, is_url=True)
                if not job_url or job_url in processed_urls:
                    logger.debug("[camhr] Skipping seen URL: %s", job_url)
                    continue
                jid = make_job_id(job_url)
                if jid in processed_ids:
                    logger.debug("[camhr] Skipping seen ID %s", jid)
                    continue

                logger.info("[camhr] Fetching detail for job_id=%s", job_id)
                detail = self._fetch_detail(job_id) if job_id else {}

                try:
                    fields = self._build_record(list_job, detail, job_url)
                except Exception as e:
                    logger.warning("[camhr] Failed to build record for %s: %s", job_url, e)
                    continue

                if not sanitize_text(fields.get("Job Title", "")):
                    logger.warning("[camhr] No title for %s — skipping", job_url)
                    continue

                new_on_page += 1
                logger.info("[camhr] Extracted title: '%s'", fields["Job Title"])

                record = empty_record()
                record.update({k: v for k, v in fields.items() if v})
                record["Job URL"] = job_url

                mined = mine_fields(record.get("Job Description", ""))
                for k, v in mined.items():
                    if not sanitize_text(record.get(k, "")):
                        record[k] = v

                if not record.get("Job Location"):
                    record["Job Location"] = self.default_location
                record["Job Type"] = normalise_job_type(
                    record.get("Job Type", "")).replace("-", " ").title()
                record["Date Posted"] = parse_date(record.get("Date Posted", ""),
                                                   fallback_today=True)
                record["Deadline"] = parse_date(record.get("Deadline", ""))
                record["Estimated Deadline"] = estimated_deadline(
                    record["Date Posted"], record["Deadline"])

                raw_desc     = record.get("Job Description", "")
                cleaned_desc = clean_description(raw_desc)
                if cleaned_desc != raw_desc:
                    logger.info("[camhr] clean_description removed %d chars from '%s'",
                                len(raw_desc) - len(cleaned_desc), record.get("Job Title", ""))
                record["Job Description"] = cleaned_desc

                logger.info(
                    "[camhr] Record ready — Company='%s' | Location='%s' | "
                    "Posted='%s' | Deadline='%s' | Application=%r",
                    record.get("Company Name", ""),
                    record.get("Job Location", ""),
                    record.get("Date Posted", ""),
                    record.get("Estimated Deadline", ""),
                    record.get("Application", "")[:80],
                )

                record["_job_id"] = jid
                processed_ids.add(jid)
                processed_urls.add(job_url)
                yielded += 1
                yield record

            logger.info("[camhr] Page %d: %d new job(s) (total yielded %d)",
                        page, new_on_page, yielded)
            page += 1

        logger.info("[CAMHR] Scrape complete — yielded %d record(s)", yielded)


# ════════════════════════════════════════════════════════════════════════════════
# Source registry
# ════════════════════════════════════════════════════════════════════════════════
SOURCE_REGISTRY = {
    "camhr": CamHRScraper,
}
_ALL_SOURCES = list(SOURCE_REGISTRY.keys())


# ════════════════════════════════════════════════════════════════════════════════
# Orchestration helpers
# ════════════════════════════════════════════════════════════════════════════════
def _needs_enrichment(rec: dict) -> bool:
    if not has_application(rec):
        return True
    blanks = sum(1 for f in COMPANY_FIELDS if not sanitize_text(rec.get(f, "")))
    return blanks >= 3


def _append_csv(rec: dict):
    write_header = not os.path.exists(OUTPUT_CSV)
    with open(OUTPUT_CSV, "a", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=APPSCRIPT_COLUMNS)
        if write_header:
            w.writeheader()
        w.writerow({c: rec.get(c, "") for c in APPSCRIPT_COLUMNS})


# ════════════════════════════════════════════════════════════════════════════════
# main()
# ════════════════════════════════════════════════════════════════════════════════
def main():
    ap = argparse.ArgumentParser(
        description="CamHR Cambodia job scraper → WordPress",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=f"Available sources: {', '.join(_ALL_SOURCES)}",
    )
    ap.add_argument("--limit",         type=int, default=DEFAULT_LIMIT,
                    help=f"max jobs per source (default: {DEFAULT_LIMIT}; 0=unlimited)")
    ap.add_argument("--sources",       nargs="+", default=_ALL_SOURCES,
                    choices=_ALL_SOURCES, metavar="SOURCE",
                    help=f"sources to run (default: all). choices: {_ALL_SOURCES}")
    ap.add_argument("--dry-run",       action="store_true",
                    help="scrape + paraphrase but do NOT post to WordPress")
    ap.add_argument("--no-paraphrase", action="store_true",
                    help="post original text without Mistral paraphrasing")
    ap.add_argument("--verbose",       action="store_true",
                    help="enable DEBUG-level logging")
    args = ap.parse_args()

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
        logger.setLevel(logging.DEBUG)

    do_paraphrase = not args.no_paraphrase

    logger.info("=" * 60)
    logger.info("Cambodia CamHR Job Scraper")
    logger.info("Sources   : %s", ", ".join(args.sources))
    logger.info("Limit     : %s jobs/source", str(args.limit) if args.limit else "unlimited")
    logger.info("Dry-run   : %s", args.dry_run)
    logger.info("Paraphrase: %s", do_paraphrase)
    logger.info("=" * 60)

    http     = HttpClient()
    enricher = CompanyEnricher(http)
    para     = Paraphraser()

    wp = None
    if not args.dry_run:
        wp = WordPressClient()

    processed_ids, processed_urls = tracker_load()
    logger.info("Tracker: %d previously processed IDs / %d URLs loaded",
                len(processed_ids), len(processed_urls))

    seen_fingerprints, fingerprint_index = tracker_load_fingerprints()
    logger.info("Tracker: %d fingerprints loaded (%d for fuzzy match)",
                len(seen_fingerprints), len(fingerprint_index))
    FUZZY_DUP_THRESHOLD = 0.86

    global_stats: dict[str, dict[str, int]] = {}

    for source_key in args.sources:
        cls     = SOURCE_REGISTRY[source_key]
        scraper = cls(http)
        stats   = {"scraped": 0, "skipped_no_app": 0,
                   "skipped_duplicate": 0, "posted": 0, "failed": 0}
        global_stats[source_key] = stats

        logger.info("")
        logger.info("╔══════════════════════════════════════╗")
        logger.info("║  SOURCE: %-28s ║", source_key.upper())
        logger.info("║  URL   : %-28s ║", cls.base_url)
        logger.info("╚══════════════════════════════════════╝")

        for rec in scraper.run(args.limit, processed_ids, processed_urls):
            jid     = rec.pop("_job_id")
            title   = rec.get("Job Title", "")
            company = rec.get("Company Name", "")
            fp      = make_fingerprint(title, company)

            tracker_mark_read(jid, source_key, rec.get("Job URL", ""),
                              title, company, fingerprint=fp)
            stats["scraped"] += 1
            logger.info("[%s] ── Job #%d ──  '%s'  @  '%s'",
                        source_key, stats["scraped"], title, company)

            # Cross-source duplicate check
            is_dup, dup_reason = False, ""
            if fp in seen_fingerprints:
                is_dup     = True
                dup_reason = "exact fingerprint match"
            else:
                for prior in fingerprint_index:
                    if prior["source"] == source_key:
                        continue
                    sim = fingerprint_similarity(title, company,
                                                 prior["title"], prior["company"])
                    if sim >= FUZZY_DUP_THRESHOLD:
                        is_dup     = True
                        dup_reason = (
                            f"fuzzy match (sim={sim:.2f}) with '{prior['title']}' "
                            f"@ '{prior['company']}' [{prior['source']}]"
                        )
                        break

            if is_dup:
                logger.info("[%s] Duplicate skipped — %s", source_key, dup_reason)
                tracker_mark_failed(jid, f"duplicate|{dup_reason}"[:120])
                stats["skipped_duplicate"] += 1
                continue

            seen_fingerprints.add(fp)
            fingerprint_index.append({
                "fingerprint": fp, "title": title,
                "company": company, "source": source_key,
            })

            # Enrichment
            if _needs_enrichment(rec):
                logger.info("[%s] Enriching company data for '%s'", source_key, company or title)
                rec = enricher.enrich(rec)
                logger.info(
                    "[%s] Post-enrichment: app=%r  website=%r  logo=%r",
                    source_key,
                    rec.get("Application", "")[:60],
                    rec.get("Company Website", "")[:60],
                    rec.get("Company Logo", "")[:60],
                )

            # Require application route
            if not has_application(rec):
                logger.info("[%s] No valid application route — skipping '%s'",
                            source_key, title)
                tracker_mark_failed(jid, "no application route")
                stats["skipped_no_app"] += 1
                _append_csv(rec)
                continue

            logger.info("[%s] Application route: %s", source_key, rec.get("Application", ""))
            _append_csv(rec)

            # Paraphrase
            if do_paraphrase:
                logger.info("[%s] Paraphrasing title + description…", source_key)
                out_title   = para.title(title)
                out_desc    = para.description(rec.get("Job Description", ""))
                out_company = (para.company(rec.get("Company Details", ""))
                               if rec.get("Company Details") else "")
                logger.info("[%s] Paraphrased title: '%s' → '%s'",
                            source_key, title, out_title)
            else:
                out_title   = title
                out_desc    = rec.get("Job Description", "")
                out_company = rec.get("Company Details", "")

            # Post to WordPress
            if args.dry_run:
                logger.info("[%s] [dry-run] Would post: '%s'", source_key, out_title)
                continue

            try:
                co_id, co_url = wp.save_company(rec, out_company, tagline="")
                if co_id:
                    logger.info("[%s] Company saved: WP ID %s  %s",
                                source_key, co_id, co_url)
                wp_id, wp_url = wp.save_job(rec, out_title, out_desc)
                if wp_id:
                    tracker_mark_posted(jid, wp_id, wp_url)
                    stats["posted"] += 1
                    logger.info("[%s] Posted: WP ID %s  %s", source_key, wp_id, wp_url)
                else:
                    tracker_mark_failed(jid, "wp post returned no id")
                    stats["failed"] += 1
                    logger.error("[%s] WP post returned no ID for '%s'", source_key, title)
            except Exception as e:
                logger.error("[%s] Posting exception for '%s': %s", source_key, title, e)
                tracker_mark_failed(jid, e)
                stats["failed"] += 1

    # Summary
    logger.info("")
    logger.info("╔══════════════════════════════════════════════════════════════════════╗")
    logger.info("║                        PER-SOURCE SUMMARY                           ║")
    logger.info("╠══════════════════════════════════════════════════════════════════════╣")
    total = {"scraped": 0, "skipped_no_app": 0, "skipped_duplicate": 0,
             "posted": 0, "failed": 0}
    for src, s in global_stats.items():
        logger.info(
            "║  %-16s scraped=%-4d posted=%-4d skip_app=%-4d dup=%-4d fail=%-4d  ║",
            src, s["scraped"], s["posted"], s["skipped_no_app"],
            s.get("skipped_duplicate", 0), s["failed"],
        )
        for k in total:
            total[k] += s.get(k, 0)
    logger.info("╠══════════════════════════════════════════════════════════════════════╣")
    logger.info(
        "║  %-16s scraped=%-4d posted=%-4d skip_app=%-4d dup=%-4d fail=%-4d  ║",
        "TOTAL", total["scraped"], total["posted"],
        total["skipped_no_app"], total["skipped_duplicate"], total["failed"],
    )
    logger.info("╚══════════════════════════════════════════════════════════════════════╝")

    tracker_summary()
    logger.info(
        "DONE %s | scraped=%d posted=%d skip_app=%d dup=%d failed=%d",
        datetime.now().strftime("%Y-%m-%d %H:%M"),
        total["scraped"], total["posted"],
        total["skipped_no_app"], total["skipped_duplicate"], total["failed"],
    )


if __name__ == "__main__":
    main()

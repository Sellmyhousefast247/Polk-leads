#!/usr/bin/env python3
"""CI entrypoint for the Polk scraper.

Wraps fetch.main() with one extra hardening step: the browserviewor
api/search endpoint sits behind an ASP.NET app that may want session
cookies, so before every probe we GET the app page to establish them,
and we log the probe's HTTP status for diagnosis.  Everything else is
identical to running scraper/fetch.py directly.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import fetch  # noqa: E402
from fetch import ClerkScraper, CLERK_APP_URL, CLERK_SEARCH_URL, log  # noqa: E402


def _alive(self):
    try:
        r0 = self.session.get(CLERK_APP_URL, timeout=self.PROBE_TIMEOUT)
        log.info("Clerk app page HTTP %s", r0.status_code)
    except Exception as exc:
        log.warning("Clerk app page unreachable: %s", exc)
    try:
        r = self.session.post(
            CLERK_SEARCH_URL,
            json=self._payload("LP", self.default_end, self.default_end),
            timeout=self.PROBE_TIMEOUT)
        log.info("Clerk probe HTTP %s: %s", r.status_code, r.text[:120])
        return r.status_code == 200
    except Exception as exc:
        log.warning("Clerk probe error: %s", exc)
        return False


ClerkScraper._alive = _alive

if __name__ == "__main__":
    fetch.main()

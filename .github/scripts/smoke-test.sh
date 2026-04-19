#!/usr/bin/env bash
# ============================================================
# Post-deploy smoke test for https://taulib.site
# ============================================================
# Fails loudly if any critical URL regresses or any expected
# body content goes missing after a Pages deployment.
#
# Invoked from .github/workflows/docs.yml after `Deploy to
# GitHub Pages` completes. Runs in <60s total.
#
# Exit codes:
#   0 — all checks passed
#   1 — one or more checks failed
#   2 — usage error
#
# Local run:
#   ./smoke-test.sh https://taulib.site
# ============================================================

set -u

BASE="${1:-https://taulib.site}"
CURL_OPTS=(--silent --show-error --max-time 10 --retry 5 --retry-delay 10 --retry-all-errors)

FAILED=0
CHECK_COUNT=0

pass() { echo "  ✓ $*"; CHECK_COUNT=$((CHECK_COUNT+1)); }
fail() { echo "  ✗ $*"; CHECK_COUNT=$((CHECK_COUNT+1)); FAILED=$((FAILED+1)); }

check_200() {
  local path="$1"
  local code
  code=$(curl "${CURL_OPTS[@]}" -o /dev/null -w '%{http_code}' "${BASE}${path}" 2>/dev/null || echo "curl-error")
  if [ "$code" = "200" ]; then
    pass "HTTP 200  ${path}"
  else
    fail "HTTP ${code}  ${path}"
  fi
}

# body_check_contains <body-var-content> <needle> <label>
body_check_contains() {
  local body="$1"
  local needle="$2"
  local label="$3"
  if printf '%s' "$body" | grep -qF -- "$needle"; then
    pass "${label}"
  else
    fail "${label}"
  fi
}

# body_check_count <body-var-content> <needle> <expected-count> <label>
body_check_count() {
  local body="$1"
  local needle="$2"
  local expected="$3"
  local label="$4"
  local count
  count=$(printf '%s' "$body" | grep -cF -- "$needle")
  if [ "$count" = "$expected" ]; then
    pass "${label}  (count=${expected})"
  else
    fail "${label}  (expected ${expected}, got ${count})"
  fi
}

# body_check_absent <body-var-content> <needle> <label>
body_check_absent() {
  local body="$1"
  local needle="$2"
  local label="$3"
  local count
  count=$(printf '%s' "$body" | grep -cF -- "$needle")
  if [ "$count" = "0" ]; then
    pass "${label}"
  else
    fail "${label}  (found ${count} occurrence(s) — regression)"
  fi
}

echo "═══════════════════════════════════════════════════════════"
echo " Post-deploy smoke test against ${BASE}"
echo "═══════════════════════════════════════════════════════════"
echo ""

echo "── HTTP 200 on every must-reach URL ───────────────────────"
for path in \
  "/" \
  "/docs/" \
  "/robots.txt" \
  "/sitemap.xml" \
  "/assets/og-image.png" \
  "/assets/favicon.svg" \
  "/assets/favicon-32x32.png" \
  "/assets/favicon-16x16.png" \
  "/assets/apple-touch-icon.png" \
  "/assets/site.webmanifest" \
  "/assets/css/main.css" \
  "/pagefind/pagefind.js" \
  "/pagefind/pagefind-ui.js" \
  "/pagefind/pagefind-ui.css"
do
  check_200 "$path"
done

echo ""
echo "── Fetching homepage body once for integrity checks ──────"
HOME_BODY=$(curl "${CURL_OPTS[@]}" "${BASE}/" 2>/dev/null || echo "")
if [ -z "$HOME_BODY" ]; then
  fail "homepage fetch failed — aborting body checks"
  echo "═══════════════════════════════════════════════════════════"
  echo " ✗ ${FAILED} of ${CHECK_COUNT} checks FAILED"
  exit 1
fi
echo "  (fetched ${#HOME_BODY} bytes)"

echo ""
echo "── Homepage body integrity ────────────────────────────────"
body_check_count    "$HOME_BODY" "<title>"                              "1"  "single <title> (no jekyll-seo-tag duplicate)"
body_check_contains "$HOME_BODY" 'name="theme-color"'                        "theme-color meta present"
body_check_contains "$HOME_BODY" "#163e64"                                   "canonical navy #163e64 in head"
body_check_contains "$HOME_BODY" "orcid.org/0009-0007-0718-1042"             "Thorsten ORCID in JSON-LD"
body_check_contains "$HOME_BODY" "orcid.org/0009-0007-3495-7416"             "Anna-Sophie ORCID in JSON-LD"
body_check_contains "$HOME_BODY" "https://taulib.site/assets/og-image.png"   "og:image absolute URL"
body_check_contains "$HOME_BODY" "Panta-Rhei-Research/taulib"                "canonical GitHub org in links"

echo ""
echo "── Anti-regression checks (zero-occurrence) ──────────────"
body_check_absent "$HOME_BODY" "Panta-Rhei-Framework"                   "no deprecated org references"
body_check_absent "$HOME_BODY" "/Users/thorfuchs"                       "no local filesystem paths leaked"
body_check_absent "$HOME_BODY" "#294b66"                                "no pre-migration accent color"

echo ""
echo "── robots.txt + sitemap.xml integrity ────────────────────"
ROBOTS=$(curl "${CURL_OPTS[@]}" "${BASE}/robots.txt" 2>/dev/null || echo "")
body_check_contains "$ROBOTS" "Content-Signal"                "Content-Signal directive present"
body_check_contains "$ROBOTS" "Sitemap: https://taulib.site"  "sitemap reference present"

SITEMAP=$(curl "${CURL_OPTS[@]}" "${BASE}/sitemap.xml" 2>/dev/null || echo "")
loc_count=$(printf '%s' "$SITEMAP" | grep -c '<loc>' || true)
if [ "$loc_count" -ge 400 ]; then
  pass "sitemap has ${loc_count} URLs (expected ≥400 after doc-gen4 build)"
else
  fail "sitemap has only ${loc_count} URLs (expected ≥400 after doc-gen4 build)"
fi
CHECK_COUNT=$((CHECK_COUNT+1))

echo ""
echo "═══════════════════════════════════════════════════════════"
if [ "$FAILED" -eq 0 ]; then
  echo " ✓ ALL ${CHECK_COUNT} CHECKS PASSED"
  echo "═══════════════════════════════════════════════════════════"
  exit 0
else
  echo " ✗ ${FAILED} of ${CHECK_COUNT} checks FAILED"
  echo "═══════════════════════════════════════════════════════════"
  exit 1
fi

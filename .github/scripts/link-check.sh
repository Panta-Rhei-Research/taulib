#!/usr/bin/env bash
# ============================================================
# Dead-link audit for taulib.site
# ============================================================
# Runs html-proofer against the built site/_site/ tree after
# Jekyll + Pagefind + doc-gen4 extraction. Internal-only
# (external link validation is a separate, slower check).
#
# Fails the build visibly if any NEW broken internal link appears.
# Known-broken URL patterns are in IGNORE_URLS below.
#
# Usage:
#   ./link-check.sh [path/to/_site]
# ============================================================

set -u

SITE="${1:-site/_site}"
if [ ! -d "$SITE" ]; then
  echo "ERROR: $SITE is not a directory"
  echo "Usage: $0 <path-to-_site>"
  exit 2
fi

export LANG=en_US.UTF-8
export LC_ALL=en_US.UTF-8

# Ignore patterns: /regex/ for patterns, bare strings for literals.
# Pagefind assets carry ?v=<epoch> cache-bust which html-proofer
# doesn't strip before the file-exists check.
IGNORE_URLS=$(cat <<'EOF' | tr '\n' ',' | sed 's/,$//'
/\/pagefind\//
EOF
)

echo "═══════════════════════════════════════════════════════════"
echo " Dead-link audit against ${SITE}/"
echo "═══════════════════════════════════════════════════════════"
echo ""

cd site
bundle exec htmlproofer _site \
  --disable-external \
  --checks Links,Images,Scripts \
  --ignore-missing-alt \
  --no-check-internal-hash \
  --ignore-urls "$IGNORE_URLS"

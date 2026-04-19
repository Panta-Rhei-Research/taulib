#!/usr/bin/env bash
# ============================================================
# Dead-link audit for taulib.site
# ============================================================
# Runs html-proofer against the built site/_site/ tree after
# Jekyll + Pagefind + doc-gen4 extraction. Internal-only.
#
# Scope: Jekyll shell pages only (homepage + /docs/ index + any
# hand-authored Jekyll surfaces). The 460 auto-generated doc-gen4
# module pages are EXCLUDED because:
#
#   1. Their internal cross-refs use relative paths like
#      `../../.././TauLib/BookX/Y.html#SymbolName` — html-proofer
#      can't resolve these statically (they depend on doc-gen4's
#      runtime resolution).
#
#   2. Many refs are to filtered-out upstream libs (Init/, Std/,
#      Mathlib/, Lean/, Aesop/, Batteries/) — intentionally
#      broken by filter_docs.py to keep the bundle tight.
#
#   3. Link-integrity of doc-gen4 output is doc-gen4's job, not
#      ours. If a TauLib module refactor breaks a cross-ref,
#      that's caught by `lake build TauLib:docs` which runs
#      earlier in the same workflow.
#
# What we DO check: homepage, /docs/ index, any future hand-
# authored Jekyll pages that sit alongside the doc-gen4 tree.
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

IGNORE_URLS='/\/pagefind\//'

# Exclude the doc-gen4 module pages. Slug convention is `book-<roman>-<rest>`
# plus `tour-*` for the guided tour pages. The Jekyll-rendered `/docs/index.html`
# is kept in scope.
IGNORE_FILES='/\/docs\/book-/,/\/docs\/tour-/'

echo "═══════════════════════════════════════════════════════════"
echo " Dead-link audit against ${SITE}/"
echo " Scope: Jekyll shell only (doc-gen4 module pages excluded)"
echo "═══════════════════════════════════════════════════════════"
echo ""

cd site
bundle exec htmlproofer _site \
  --disable-external \
  --checks Links,Images,Scripts \
  --ignore-missing-alt \
  --no-check-internal-hash \
  --ignore-urls "$IGNORE_URLS" \
  --ignore-files "$IGNORE_FILES"

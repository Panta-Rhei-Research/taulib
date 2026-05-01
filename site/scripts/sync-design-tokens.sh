#!/usr/bin/env bash
# ================================================================
# sync-design-tokens.sh
# ================================================================
# Re-pulls the canonical design tokens (and selected partner files)
# from the panta-rhei.site repo into taulib.site.
#
# Strategy: Copy + sync discipline (Workstream W1, plan-mode 2026-05-01).
# panta-rhei.site is the canonical source for shared brand design;
# taulib.site copies in via this script and adds a `// Synced from ...`
# header banner so it's obvious the files are mirrors.
#
# Re-run cadence: once per panta-rhei.site release / token revision.
# After running, review the diff before committing.
#
# Usage:
#   cd taulib/site
#   bash scripts/sync-design-tokens.sh
#   git diff _sass/ assets/brand/   # review changes
# ================================================================

set -euo pipefail

# Locate repos. Default to sibling layout under ~/Panta-Rhei-Research/.
TAULIB_SITE="${TAULIB_SITE:-$(cd "$(dirname "$0")/.." && pwd)}"

# Auto-detect panta-rhei.site location. Walk up from TAULIB_SITE looking
# for a sibling 'site' directory that is the panta-rhei.site canonical
# checkout. Heuristic: panta-rhei.site has the brand-glyph SVG; taulib's
# own site/ may not (especially before this wave runs). Falls back to
# checking that the path is OUTSIDE the taulib repo entirely.
if [[ -z "${PANTA_SITE:-}" ]]; then
  # Find the taulib repo root (walk up from TAULIB_SITE until we leave the
  # 'taulib' directory subtree).
  _taulib_root="$TAULIB_SITE"
  while [[ "$_taulib_root" != "/" && "$(basename "$_taulib_root")" != "taulib" ]]; do
    _taulib_root="$(cd "$_taulib_root/.." && pwd)"
  done
  # Now walk up from taulib root, looking for sibling panta-rhei.site
  _candidate="$_taulib_root"
  while [[ "$_candidate" != "/" ]]; do
    _candidate="$(cd "$_candidate/.." && pwd)"
    _maybe="$_candidate/site"
    # Confirm this is panta-rhei.site by checking for the brand-glyph marker
    if [[ -d "$_maybe/_sass" && -f "$_maybe/assets/brand/logo-glyph.svg" ]]; then
      PANTA_SITE="$(cd "$_maybe" && pwd)"
      break
    fi
  done
fi

if [[ ! -d "$PANTA_SITE/_sass" ]]; then
  echo "ERROR: panta-rhei.site _sass/ not found at: $PANTA_SITE/_sass"
  echo "Set PANTA_SITE=/path/to/panta-rhei-site/repo and re-run."
  exit 1
fi

echo "Source: $PANTA_SITE"
echo "Target: $TAULIB_SITE"
echo

# ----------------------------------------------------------------
# Files to sync verbatim from panta-rhei.site to taulib.site
# ----------------------------------------------------------------
# Each entry: SOURCE_PATH (relative to panta-rhei) → TARGET_PATH (relative to taulib)
SYNCED_FILES=(
  "_sass/_variables.scss:_sass/_variables.scss"
  "assets/brand/logo-glyph.svg:assets/brand/logo-glyph.svg"
  "assets/brand/logo-horizontal.svg:assets/brand/logo-horizontal.svg"
  "assets/brand/logo-mono-white.svg:assets/brand/logo-mono-white.svg"
)

SYNC_BANNER='// ================================================================
// SYNCED FROM panta-rhei.site — DO NOT EDIT IN PLACE
// Source: panta-rhei.site/SOURCE_PATH
// Sync mechanism: taulib/site/scripts/sync-design-tokens.sh
// To update: edit upstream in panta-rhei.site/_sass, then re-run sync.
// ================================================================
'

for entry in "${SYNCED_FILES[@]}"; do
  src="${entry%%:*}"
  dst="${entry##*:}"
  src_path="$PANTA_SITE/$src"
  dst_path="$TAULIB_SITE/$dst"

  if [[ ! -f "$src_path" ]]; then
    echo "  SKIP (missing source): $src"
    continue
  fi

  mkdir -p "$(dirname "$dst_path")"

  # Add sync banner ONLY for SCSS files (SVGs/PNGs left as-is)
  if [[ "$dst" == *.scss ]]; then
    banner="${SYNC_BANNER//SOURCE_PATH/$src}"
    { printf '%s\n' "$banner"; cat "$src_path"; } > "$dst_path"
    echo "  SYNCED (with banner): $src → $dst"
  else
    cp "$src_path" "$dst_path"
    echo "  SYNCED:                $src → $dst"
  fi
done

# ----------------------------------------------------------------
# Taulib-specific transformation: strip the .lane-* class declarations
# from _variables.scss (per Workstream W1, decision 3 — keep the CSS
# custom-properties for component compat, but no lane CLASSES on
# taulib.site since taulib is single-purpose).
# ----------------------------------------------------------------
VARS="$TAULIB_SITE/_sass/_variables.scss"
if [[ -f "$VARS" ]] && grep -q "^\.lane-" "$VARS"; then
  # Replace the 9 .lane-* class declarations with a single explanatory comment.
  # The CSS custom-properties --lane-* in :root are preserved (lines 121–140).
  python3 - <<'PY' "$VARS"
import sys, re
path = sys.argv[1]
content = open(path).read()
# Strip every individual .lane-* { ... } class declaration line.
lane_re = re.compile(r'^\.lane-[a-z]+ \{[^}]+\}\n', re.MULTILINE)
new_content, n = lane_re.subn('', content)
# Drop any prior taulib transformation comment block from earlier runs
prior_comment_re = re.compile(
    r'^// taulib\.site transformation: lane CLASSES stripped[^\n]*\n'
    r'(// [^\n]*\n)+',
    re.MULTILINE
)
new_content = prior_comment_re.sub('', new_content)
# Append the canonical explanatory comment ONCE at the bottom
if n > 0 and "taulib.site transformation: lane CLASSES stripped" not in new_content:
    new_content = new_content.rstrip() + "\n\n" + (
        "// taulib.site transformation: lane CLASSES stripped per Workstream W1,\n"
        "// decision 3. The lane CSS custom-properties (--lane-*) in :root above\n"
        "// are preserved for any shared component that references them; taulib.site\n"
        "// is single-purpose Lean docs, so no lane-classes are attached to pages.\n"
    )
open(path, 'w').write(new_content)
if n > 0:
    print(f"  TRANSFORMED:           stripped {n} .lane-* class declaration(s)")
PY
fi

echo
echo "Sync complete. Run 'git diff' to review."

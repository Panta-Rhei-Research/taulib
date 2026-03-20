#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# TauLib Documentation Build Script
# ============================================================
# Usage: ./scripts/build_docs.sh [OPTIONS]
#
# Options:
#   --skip-lake-build   Skip lake build (reuse existing oleans)
#   --skip-docgen       Skip doc-gen4 build (reuse existing HTML)
#   --skip-filter       Skip TauLib-only filtering (keep all deps)
#   --skip-stats        Skip statistics dashboard generation
#   --skip-depgraph     Skip dependency graph generation
#   --registry-dir DIR  Override registry directory path
#
# Builds doc-gen4 HTML documentation with all enhancements:
#   1. lake build TauLib             (compile library)
#   2. lake build TauLib:docs        (generate raw doc-gen4 output)
#   3. python3 filter_docs.py        (strip non-TauLib content)
#   4. cat taulib_theme.css >> ...   (apply CSS theme)
#   5. inject landing_page.html      (replace index.html content)
#   6. python3 generate_stats.py     (statistics dashboard)
#   7. python3 generate_depgraph.py  (dependency graph)
#
# Output: docbuild/.lake/build/doc/ (ready to serve or deploy)
# All links are relative — hosting-agnostic.
# ============================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TAULIB_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DOCBUILD="$TAULIB_ROOT/docbuild"
DOC_OUTPUT="$DOCBUILD/.lake/build/doc"

# Default registry path: registry/ in the TauLib repo root
REGISTRY_DIR="${TAULIB_ROOT}/registry"

SKIP_LAKE_BUILD=false
SKIP_DOCGEN=false
SKIP_FILTER=false
SKIP_STATS=false
SKIP_DEPGRAPH=false

for arg in "$@"; do
  case $arg in
    --skip-lake-build) SKIP_LAKE_BUILD=true ;;
    --skip-docgen)     SKIP_DOCGEN=true ;;
    --skip-filter)     SKIP_FILTER=true ;;
    --skip-stats)      SKIP_STATS=true ;;
    --skip-depgraph)   SKIP_DEPGRAPH=true ;;
    --registry-dir=*)  REGISTRY_DIR="${arg#*=}" ;;
    --registry-dir)    shift; REGISTRY_DIR="$1" ;;
    *) echo "Unknown argument: $arg"; exit 1 ;;
  esac
done

echo "=== TauLib Documentation Build ==="
echo "Root:     $TAULIB_ROOT"
echo "Output:   $DOC_OUTPUT"
echo "Registry: $REGISTRY_DIR"
echo ""

# ----------------------------------------------------------
# Step 1: Build TauLib (ensure oleans are current)
# ----------------------------------------------------------
if [ "$SKIP_LAKE_BUILD" = false ]; then
  echo "--- Step 1/7: Building TauLib ---"
  cd "$TAULIB_ROOT"
  lake build
  echo ""
fi

# ----------------------------------------------------------
# Step 2: Build doc-gen4 documentation
# ----------------------------------------------------------
if [ "$SKIP_DOCGEN" = false ]; then
  echo "--- Step 2/7: Building doc-gen4 documentation ---"
  cd "$DOCBUILD"
  if [ ! -f lake-manifest.json ]; then
    echo "  Initializing docbuild dependencies..."
    MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
  fi
  lake build TauLib:docs
  echo ""
fi

# Verify output exists
if [ ! -d "$DOC_OUTPUT" ]; then
  echo "ERROR: Doc output directory not found at $DOC_OUTPUT"
  echo "  Run without --skip-docgen first."
  exit 1
fi

# ----------------------------------------------------------
# Step 3: Filter to TauLib-only content
# ----------------------------------------------------------
if [ "$SKIP_FILTER" = false ]; then
  echo "--- Step 3/7: Filtering to TauLib-only content ---"
  python3 "$SCRIPT_DIR/filter_docs.py" --doc-dir "$DOC_OUTPUT"
  echo ""
fi

# ----------------------------------------------------------
# Step 4: Apply CSS theme
# ----------------------------------------------------------
echo "--- Step 4/7: Applying Panta Rhei CSS theme ---"
if [ -f "$SCRIPT_DIR/taulib_theme.css" ]; then
  # Only append if not already appended (idempotent)
  if ! grep -q "TauLib / Panta Rhei — Documentation Theme" "$DOC_OUTPUT/style.css" 2>/dev/null; then
    cat "$SCRIPT_DIR/taulib_theme.css" >> "$DOC_OUTPUT/style.css"
    echo "  CSS theme appended to style.css"
  else
    echo "  CSS theme already present in style.css (skipped)"
  fi
  # Copy self-hosted Manrope font files
  if [ -d "$SCRIPT_DIR/fonts" ]; then
    mkdir -p "$DOC_OUTPUT/fonts"
    cp "$SCRIPT_DIR/fonts/"*.woff2 "$DOC_OUTPUT/fonts/" 2>/dev/null
    echo "  Manrope font files copied to doc output"
  fi
else
  echo "  WARNING: scripts/taulib_theme.css not found, skipping theme"
fi
echo ""

# ----------------------------------------------------------
# Step 5: Replace landing page
# ----------------------------------------------------------
echo "--- Step 5/7: Replacing landing page ---"
if [ -f "$SCRIPT_DIR/landing_page.html" ]; then
  python3 -c "
import re, sys
with open('$DOC_OUTPUT/index.html') as f:
    html = f.read()
with open('$SCRIPT_DIR/landing_page.html') as f:
    content = f.read()
new_html = re.sub(
    r'(<main>).*?(</main>)',
    lambda m: m.group(1) + '\n' + content + '\n' + m.group(2),
    html, flags=re.DOTALL)
if new_html == html:
    print('  WARNING: <main> tags not found, trying <div class=\"main\"> pattern', file=sys.stderr)
    # Fallback: try <div class=\"main\"> ... </div>
    new_html = re.sub(
        r'(<div\s+class=\"main\">).*?(</div>\s*</body>)',
        lambda m: m.group(1) + '\n' + content + '\n' + m.group(2),
        html, flags=re.DOTALL)
with open('$DOC_OUTPUT/index.html', 'w') as f:
    f.write(new_html)
print('  Landing page replaced successfully')
"
else
  echo "  WARNING: scripts/landing_page.html not found, skipping"
fi
echo ""

# ----------------------------------------------------------
# Step 6: Generate statistics dashboard
# ----------------------------------------------------------
if [ "$SKIP_STATS" = false ]; then
  echo "--- Step 6/7: Generating statistics dashboard ---"
  if [ -d "$REGISTRY_DIR" ]; then
    python3 "$SCRIPT_DIR/generate_stats.py" \
      --output "$DOC_OUTPUT/stats.html" \
      --registry-dir "$REGISTRY_DIR" \
      --lean-src "$TAULIB_ROOT/TauLib"
  else
    echo "  WARNING: Registry directory not found at $REGISTRY_DIR, skipping stats"
  fi
  echo ""
fi

# ----------------------------------------------------------
# Step 7: Generate dependency graph
# ----------------------------------------------------------
if [ "$SKIP_DEPGRAPH" = false ]; then
  echo "--- Step 7/7: Generating dependency graph ---"
  if [ -d "$REGISTRY_DIR" ]; then
    python3 "$SCRIPT_DIR/generate_depgraph.py" \
      --output "$DOC_OUTPUT/depgraph.html" \
      --registry-dir "$REGISTRY_DIR"
  else
    echo "  WARNING: Registry directory not found at $REGISTRY_DIR, skipping depgraph"
  fi
  echo ""
fi

# ----------------------------------------------------------
# Summary
# ----------------------------------------------------------
MODULE_COUNT=$(find "$DOC_OUTPUT/TauLib" -name "*.html" ! -name "*.hash" ! -name "*.trace" 2>/dev/null | wc -l | tr -d ' ')
TOTAL_HTML=$(find "$DOC_OUTPUT" -name "*.html" 2>/dev/null | wc -l | tr -d ' ')
OUTPUT_SIZE=$(du -sh "$DOC_OUTPUT" | cut -f1)

echo "============================================================"
echo "Documentation build complete"
echo "============================================================"
echo "  TauLib module pages: $MODULE_COUNT"
echo "  Total HTML files:    $TOTAL_HTML"
echo "  Output size:         $OUTPUT_SIZE"
echo ""
echo "To preview locally:"
echo "  cd $DOC_OUTPUT && python3 -m http.server 8000"
echo "  Open http://localhost:8000"
echo ""
echo "All links are relative — deploy to any static host."

#!/usr/bin/env bash
# ============================================================
# One-time hook installer — run from the repo root.
#
# Usage:
#   ./.githooks/install.sh
#
# What it does:
#   Sets `git config core.hooksPath .githooks` on this clone,
#   pointing git at the tracked hooks directory instead of the
#   default .git/hooks/. All hooks in .githooks/ then run
#   automatically on the corresponding git events.
#
# Safe to run multiple times — idempotent.
# ============================================================

set -e

# Sanity: we're in a git repo
if ! git rev-parse --git-dir >/dev/null 2>&1; then
  echo "ERROR: not inside a git repo"
  exit 1
fi

# Find the repo root
REPO_ROOT=$(git rev-parse --show-toplevel)
cd "$REPO_ROOT"

if [ ! -d ".githooks" ]; then
  echo "ERROR: .githooks/ directory not found at $REPO_ROOT"
  exit 1
fi

# Make all hook scripts executable
chmod +x .githooks/*

# Point git at our tracked hook directory
git config core.hooksPath .githooks

echo "✓ Installed git hooks from .githooks/"
echo ""
echo "Active hooks:"
for hook in .githooks/*; do
  [ -f "$hook" ] && [ "$(basename "$hook")" != "install.sh" ] && echo "  - $(basename "$hook")"
done
echo ""
echo "To bypass a hook for a single commit: git commit --no-verify"
echo "To uninstall: git config --unset core.hooksPath"

#!/usr/bin/env bash
# Checks that `PROVENANCE.md` and the book's exercises agree:
#
#   - every `(name := "…")` of an `:::exercise` block under `CSwL/` is
#     mentioned in `PROVENANCE.md`;
#   - every id in a `CSwL id` column of a table in `PROVENANCE.md` is the
#     name of an exercise under `CSwL/`.
#
# Prints each discrepancy and exits with status 1 if there is any.
#
# Usage: scripts/check-provenance.sh

set -euo pipefail

CSWL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROVENANCE="$CSWL_DIR/PROVENANCE.md"

# Names of the exercises in the book.
exercises="$(grep -rhE '^:+exercise' "$CSWL_DIR/CSwL" --include='*.lean' \
  | sed -nE 's/.*\(name := "([^"]+)"\).*/\1/p' | sort -u)"

# Ids in the `CSwL id` column of every table, skipping `—` placeholders.
cited="$(awk -F'|' '
  /^\|/ {
    if (!col) {
      for (i = 2; i < NF; i++) if ($i ~ /CSwL id/) col = i
    } else if ($col !~ /^[ -]*$/) {
      id = $col; gsub(/[ `]/, "", id)
      if (id != "—") print id
    }
    next
  }
  { col = 0 }
' "$PROVENANCE" | sort -u)"

status=0

while IFS= read -r name; do
  if ! grep -qE "(^|[^[:alnum:]_-])${name}([^[:alnum:]_-]|$)" "$PROVENANCE"; then
    echo "not in PROVENANCE.md: $name"
    status=1
  fi
done <<< "$exercises"

while IFS= read -r id; do
  [ -z "$id" ] && continue
  if ! grep -qxF "$id" <<< "$exercises"; then
    echo "no such exercise:     $id"
    status=1
  fi
done <<< "$cited"

exit $status

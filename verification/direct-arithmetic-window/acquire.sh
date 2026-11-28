#!/usr/bin/env bash
# Acquire only the pinned external source. No compiled submission cache is used.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
target="${1:?usage: acquire.sh ORIGINAL_CHECKOUT}"
mapfile -t source_pin < <(python3 - "$here/SOURCE_LOCK.json" <<'PY'
import json,sys
x=json.load(open(sys.argv[1]))['original']
print(x['repository']); print(x['commit'])
PY
)
created=false
if [[ ! -d "$target/.git" ]]; then
  test ! -e "$target"
  git clone --filter=blob:none --no-checkout "${source_pin[0]}" "$target"
  created=true
fi
git -C "$target" cat-file -e "${source_pin[1]}^{commit}" ||
  git -C "$target" fetch --no-tags --depth 1 origin "${source_pin[1]}"
if [[ "$created" == false ]]; then
  test -z "$(git -C "$target" status --porcelain --untracked-files=all)"
fi
git -C "$target" checkout --detach "${source_pin[1]}"
test "$(git -C "$target" rev-parse HEAD)" = "${source_pin[1]}"
printf 'DIRECT_WINDOW_ORIGINAL_SOURCE_LOCK_PASS %s\n' "${source_pin[1]}"

#!/usr/bin/env bash
set -euo pipefail
umask 077
d="$1"
reason="$2"
lease="$(jq -er '.lease.id' "$d/desk.json")"
status="$(curl -sS --max-time 20 -o "$d/release-response.json" -w '%{http_code}' -X POST --get --data-urlencode "lease=$lease" --data-urlencode "reason=$reason" https://pequalnp.com/desk/release)"
printf '%s %s %s\n' "$(date -u +%FT%TZ)" "$status" "$reason" | tee "$d/release-status.log"
if [[ "$status" == 200 || "$status" == 410 ]]; then
  touch "$d/done"
else
  jq 'del(.lease)' "$d/release-response.json" || true
  exit 1
fi

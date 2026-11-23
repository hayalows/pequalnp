#!/usr/bin/env bash
set -euo pipefail
umask 077
d="$1"
lease="$(jq -er '.lease.id' "$d/desk.json")"
start="$(cat "$d/start.epoch")"
while true; do
  now="$(date +%s)"
  if (( now - start >= 21000 )) || [[ -e "$d/done" ]]; then exit 0; fi
  if [[ -f "$d/last-beat" ]] && (( now - $(cat "$d/last-beat") < 570 )); then
    sleep 20
    continue
  fi
  result="$(curl -sS --max-time 15 -o "$d/beat.json" -w '%{http_code}' -X POST --get --data-urlencode "lease=$lease" https://pequalnp.com/desk/beat)" || result=transport-error
  printf '%s %s\n' "$(date -u +%FT%TZ)" "$result" >> "$d/renewals.log"
  case "$result" in
    200) date +%s > "$d/last-beat" ;;
    410) touch "$d/invalid"; exit 0 ;;
    *) sleep 30 ;;
  esac
done

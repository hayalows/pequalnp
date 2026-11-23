#!/usr/bin/env bash
set -euo pipefail
umask 077
base=/workspace/pnp-session
d="$(mktemp -d "$base/assignment.XXXXXX")"
date +%s > "$d/start.epoch"
curl -fsS --max-time 25 -o "$d/desk.json" 'https://pequalnp.com/desk/next?handle=hayalows'
printf '%s\n' "$d" > "$base/active-dir"
if jq -e '.gap != null and .lease.id != null' "$d/desk.json" >/dev/null; then
  cp "$d/start.epoch" "$d/last-beat"
  nohup bash "$base/maintain-lease.sh" "$d" > "$d/renewal-errors.log" 2>&1 < /dev/null &
  printf '%s\n' "$!" > "$d/renewal.pid"
fi
jq '{gap,shard,shards,lease: (.lease | if . == null then . else {expires_at} end),note,error}' "$d/desk.json"

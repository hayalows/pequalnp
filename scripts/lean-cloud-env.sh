#!/usr/bin/env bash
# Source in each shell. Put the selected Elan first, without duplicates.
export ELAN_HOME="${ELAN_HOME:-/workspace/.elan}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-/workspace/.cache}"
_lean_cloud_path="$ELAN_HOME/bin"
_lean_cloud_rest="${PATH-}"
while [[ -n "$_lean_cloud_rest" ]]; do
  _lean_cloud_entry="${_lean_cloud_rest%%:*}"
  [[ "$_lean_cloud_entry" == "$ELAN_HOME/bin" ]] || _lean_cloud_path+="${_lean_cloud_path:+:}$_lean_cloud_entry"
  if [[ "$_lean_cloud_rest" == *:* ]]; then _lean_cloud_rest="${_lean_cloud_rest#*:}"; else break; fi
done
export PATH="$_lean_cloud_path"
unset _lean_cloud_path _lean_cloud_rest _lean_cloud_entry
hash -r

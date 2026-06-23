#!/usr/bin/env bash
# Usage: gh-comment.sh <issue_number> <body_file>
set -euo pipefail
ISSUE="$1"; BODY_FILE="$2"
TOKEN=$(cat /tmp/.ghtok)
python3 - "$ISSUE" "$BODY_FILE" "$TOKEN" <<'PY'
import json,sys,urllib.request
issue,body_file,token=sys.argv[1],sys.argv[2],sys.argv[3]
body=open(body_file).read()
req=urllib.request.Request(
  f"https://api.github.com/repos/marcmorningstar/lean4-oseledets/issues/{issue}/comments",
  data=json.dumps({"body":body}).encode(),
  headers={"Authorization":f"token {token}","Accept":"application/vnd.github+json","Content-Type":"application/json"})
r=urllib.request.urlopen(req)
print("posted:", json.load(r)["html_url"])
PY

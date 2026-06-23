#!/usr/bin/env bash
ALERT=/workspaces/lean4-oseledets/reports/infra/ALERTS.log
while true; do
  read -r AVAIL SWAP < <(free -m | awk '/Mem:/{a=$7} /Swap:/{s=$3} END{print a, s}')
  BUILDS=$(pgrep -fc 'lake build|lake env lean' 2>/dev/null || echo 0)
  if [ "$AVAIL" -lt 4096 ]; then
    echo "$(date '+%H:%M:%S') CRITICAL avail=${AVAIL}MB swap=${SWAP}MB builds=$BUILDS" >> $ALERT
  elif [ "$AVAIL" -lt 7168 ]; then
    echo "$(date '+%H:%M:%S') WARN avail=${AVAIL}MB swap=${SWAP}MB builds=$BUILDS" >> $ALERT
  fi
  sleep 20
done

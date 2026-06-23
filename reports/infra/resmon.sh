#!/usr/bin/env bash
LOG=/workspaces/lean4-oseledets/reports/infra/resources.log
while true; do
  TS=$(date '+%Y-%m-%d %H:%M:%S')
  MEM=$(free -m | awk '/Mem:/{printf "used=%dMB free=%dMB avail=%dMB", $3,$4,$7}')
  SWAP=$(free -m | awk '/Swap:/{printf "swap_used=%dMB", $3}')
  LOAD=$(cut -d' ' -f1-3 /proc/loadavg)
  SERVE=$(pgrep -fc 'lake serve' 2>/dev/null || echo 0)
  LEAN=$(pgrep -fc '\.lake.*lean' 2>/dev/null || echo 0)
  WT=$(ls -d /home/vscode/*/ 2>/dev/null | wc -l)
  DISK=$(df -m /home/vscode | awk 'NR==2{print $4"MB free"}')
  echo "$TS | $MEM $SWAP | load=$LOAD | serve_daemons=$SERVE lean_procs=$LEAN worktrees~=$WT | disk=$DISK" >> $LOG
  sleep 45
done

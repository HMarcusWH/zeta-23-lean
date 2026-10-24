#!/bin/bash
# Worked example from Stage 18 (copy into your scratch directory and adapt; see README.md here).
# Paths come from OPICA_REPO (repository root) and OPICA_SCRATCH (scratch directory).
# Stage 18 evidence on the committed head (clean tree). Writes only into scratch.
set -u
export PATH=$HOME/.elan/bin:$PATH
REPO=${OPICA_REPO:-/home/user/zeta-23-lean}
S=${OPICA_SCRATCH:-/tmp/opica-scratch}
OUT=$S/stage18-final
C=$REPO/research/RHRC/integration/opica_followup/continuation/2026-10-22
rm -rf $OUT $S/stage18-final-runner
mkdir -p $OUT/consumers $OUT/negative-controls
cd $REPO
git rev-parse HEAD > $OUT/head.txt
git rev-parse 'HEAD^{tree}' >> $OUT/head.txt
git status --porcelain > $OUT/dirty.txt
python3 -B $C/run_candidate_checks.py --output-dir $S/stage18-final-runner > $OUT/runner.out 2>&1
echo "runner_exit=$?" > $OUT/exits.txt
cp $C/evidence/current-codex/stage5/consumers/opica-w04-w07-expected.lean $OUT/consumers/
cp $C/evidence/current-codex/stage5/consumers/opica-w06-expected.lean $OUT/consumers/
lake env lean $OUT/consumers/opica-w04-w07-expected.lean > $OUT/consumers/opica-w04-w07-expected.log 2>&1
echo "w04w07_exit=$?" >> $OUT/exits.txt
lake env lean $OUT/consumers/opica-w06-expected.lean > $OUT/consumers/opica-w06-expected.log 2>&1
echo "w06_exit=$?" >> $OUT/exits.txt
for n in negative-copoisson-jets; do
  cp $S/neg/$n.lean $REPO/lean-toolchain $OUT/negative-controls/
  (cd $OUT/negative-controls && lake --dir $REPO env lean $n.lean > $n.log 2>&1)
  echo "${n}_exit=$?" >> $OUT/exits.txt
done
echo DONE >> $OUT/exits.txt

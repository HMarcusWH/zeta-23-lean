from __future__ import annotations
import argparse, json, shutil, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; REPO=ROOT.parents[1]

def run(cmd): print('+',' '.join(map(str,cmd)),flush=True); subprocess.run(list(map(str,cmd)),cwd=REPO,check=True)

def main():
    p=argparse.ArgumentParser(); p.add_argument('--zeros',type=int,default=100); p.add_argument('--grid',type=int,default=5400); p.add_argument('--aperture-max',type=float,default=300); p.add_argument('--output-dir',type=Path,default=REPO/'rhrc_final_output'); args=p.parse_args(); args.output_dir.mkdir(parents=True,exist_ok=True)
    run([sys.executable,ROOT/'tools'/'run_suite.py'])
    r001=args.output_dir/'R001_RESULT.json'; run([sys.executable,ROOT/'routes'/'R001_exceptional_zero'/'run_experiment_cached.py','--zeros',args.zeros,'--grid',args.grid,'--aperture-max',args.aperture_max,'--output',r001])
    lean='NOT_RUN'
    if shutil.which('lake'):
        run(['lake','build','Zeta23.ExceptionalZero']); lean='PASS'
    (args.output_dir/'FORMAL_BUILD_STATUS.json').write_text(json.dumps({'lake_build_Zeta23_ExceptionalZero':lean},indent=2))
    run([sys.executable,ROOT/'runner'/'terminal_answer.py','--receipt',r001,'--output-dir',args.output_dir])
    print(f'Artifacts: {args.output_dir}')
    return 0
if __name__=='__main__': raise SystemExit(main())

import math, sys, time, importlib.util
sys.path.insert(0, '/home/user/zeta-23-lean/research/RHRC/routes/R004_prolate_v2')
spec = importlib.util.spec_from_file_location(
    "cds", "/home/user/zeta-23-lean/research/RHRC/routes/R003_ccm_bridge/check_diagonal_shift.py")
cds = importlib.util.module_from_spec(spec); spec.loader.exec_module(cds)
import mpmath as mp
mp.mp.dps = 20
from run_commutator_gauntlet_v2 import c_correction

print(f"{'lam':>5} {'c_raw(diag)':>18} {'offdiag sys':>12} {'c_corrected':>18} {'4*c_corr':>18} {'|diff|':>10} {'spread':>9}")
sys.stdout.flush()
for lam in [2.0, 3.0, 5.0, 7.0]:
    t = time.time(); L = 2*math.log(lam)
    diag = [cds.residual(n, n, L) for n in (-1, 0, 1)]
    off = [cds.residual(1, 0, L), cds.residual(2, -1, L)]
    craw = sum(diag)/len(diag); sysoff = sum(off)/len(off)
    c = craw - sysoff; pred = 4*c_correction(L); spread = max(diag)-min(diag)
    print(f"{lam:5.1f} {float(craw):18.12f} {float(sysoff):12.2e} {float(c):18.12f} "
          f"{pred:18.12f} {abs(float(c)-pred):10.2e} {float(spread):9.1e}  ({time.time()-t:.0f}s)")
    sys.stdout.flush()

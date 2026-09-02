import sys, subprocess, pickle, io, os
from pathlib import Path

PLAN = [(6,6),(8,9),(10,11),(12,13),(14,15),(16,18),(18,20),(20,22),(22,24),(24,26),
        (26,27),(28,29),(30,31),(32,33),(34,35),(36,37),(38,39),(40,41),(42,43),(44,45),
        (46,47),(48,49),(50,51),(52,53),(54,55),(56,58),(58,60),(60,63),(64,69),(70,79),(80,100)]
SCRIPTS = Path(__file__).resolve().parent
REPO = SCRIPTS.parents[0] / "Sendov" / "FiniteRange"
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_batch
ok, fail = [], []
for (n0, n1) in PLAN:
    try:
        r = gen_batch.build(n0, n1)
        pkl = SCRIPTS / f"batch_{n0}_{n1}.pkl"
        pickle.dump(r, open(pkl, "wb"))
        subprocess.run([sys.executable, str(SCRIPTS / "emit_batch.py"), str(pkl)], cwd=str(SCRIPTS), check=True)
        src = f"Degree{n0}_{n1}.lean"
        io.open(os.path.join(REPO, src), "w", encoding="utf-8", newline="\n").write(
            io.open(src, encoding="utf-8").read())
        ok.append((n0, n1))
    except Exception as e:
        print(f"  [{n0},{n1}] FAILED: {type(e).__name__}: {e}")
        fail.append((n0, n1))
    sys.stdout.flush()
print(f"\ngenerated {len(ok)} / {len(PLAN)};  failures: {fail if fail else 'none'}")

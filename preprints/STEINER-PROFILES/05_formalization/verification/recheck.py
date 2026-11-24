from pathlib import Path
import os
import subprocess
import sys

verification = Path(__file__).resolve().parent
output = Path(sys.argv[1]).resolve()
output.mkdir(parents=True, exist_ok=False)
modules_text = (verification / "MODULES.txt").read_text(encoding="utf-8")
(output / "MODULES.txt").write_text(modules_text, encoding="utf-8")
modules = modules_text.split()
environment = os.environ.copy()
environment["LEAN_NUM_THREADS"] = "1"
environment["R75_PRINT_PROOFS"] = "all"

checks = [
    ("canonical.log", ["lean", str(verification / "CheckCanonical.lean")]),
    ("catalogue.log", ["lean", str(verification / "PrintAllTheorems.lean")]),
    ("kernel.log", ["lean", "--run", str(verification / "ReplayProject.lean"), *modules]),
]
for log, command in checks:
    with (output / log).open("wb") as stream:
        subprocess.run(command, cwd=output, env=environment, stdout=stream,
                       stderr=subprocess.STDOUT, check=True)
    print(f"PASS {log}", flush=True)

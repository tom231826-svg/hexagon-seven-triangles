"""Compile one source-verified proof closure, in order, with one Lean process."""

import argparse
import hashlib
import os
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent
TARGETS = {
    "geometry": "HexagonCover.Geometry",
    "theorem": "HexagonCover.SemanticFinal",
    "all": "HexagonCover",
}
LOCAL_IMPORT = re.compile(r"^import[ \t]+(HexagonCover(?:\.\w+)*)[ \t]*$", re.M)


def verified_modules():
    modules = {}
    for entry in (ROOT / "SHA256SUMS").read_text().splitlines():
        expected, relative = entry.split("  ", 1)
        content = (ROOT / relative).read_bytes()
        if hashlib.sha256(content).hexdigest() != expected:
            raise ValueError(f"Source checksum mismatch for {relative}")
        if relative.endswith(".lean"):
            module = relative[:-5].replace("/", ".")
            modules[module] = (relative, LOCAL_IMPORT.findall(content.decode("utf-8")))
    return modules


def dependencies_first(modules, target):
    ordered = []
    complete = set()
    visiting = set()

    def visit(module):
        if module in complete:
            return
        if module in visiting:
            raise ValueError(f"Local import cycle at {module}")
        visiting.add(module)
        for dependency in modules[module][1]:
            visit(dependency)
        visiting.remove(module)
        complete.add(module)
        ordered.append(module)

    visit(target)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", choices=TARGETS, default="theorem")
    options = parser.parse_args()
    modules = verified_modules()
    order = dependencies_first(modules, TARGETS[options.target])
    env = dict(os.environ, LEAN_NUM_THREADS="1", LAKE_JOBS="1")
    env.pop("LEAN_PATH", None)
    for index, module in enumerate(order, start=1):
        source = Path(modules[module][0])
        obj = Path(".lake/build/lib/lean") / source.with_suffix(".olean")
        (ROOT / obj).parent.mkdir(parents=True, exist_ok=True)
        print(f"[{index}/{len(order)}] {module}", flush=True)
        subprocess.run(
            ["lake", "env", "lean", "-j1", "-DElab.async=false", "-o", str(obj), str(source)],
            cwd=ROOT,
            env=env,
            check=True,
        )


if __name__ == "__main__":
    main()

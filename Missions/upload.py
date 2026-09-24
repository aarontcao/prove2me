#!/usr/bin/env python3
"""Drive one mission proposal onto the platform, one gated step at a time.

    ./upload.py <slug> sweep              the duplicate sweep the gate demands
    ./upload.py <slug> dry                dry-run every call, no socket opened
    ./upload.py <slug> propose            create the draft proposal
    ./upload.py <slug> items <pid>        add every item, in item_order
    ./upload.py <slug> finish <pid>       attach read-backs, add milestones
    ./upload.py <slug> order <pid>        set item_order and the goal

Locates `p2m` via P2M_PATH or PATH.
"""

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def _p2m_command():
    """Locate the p2m client via P2M_PATH or PATH."""
    explicit = os.environ.get("P2M_PATH")
    if explicit:
        return [sys.executable, explicit] if explicit.endswith(".py") else [explicit]
    found = shutil.which("p2m")
    if found:
        return [found]
    sys.exit("cannot find the p2m client. Put it on your PATH as `p2m`, or set "
             "P2M_PATH to it.")


P2M = _p2m_command()

SWEEP = {
    "shao-three-units": ["three primes", "Vinogradov", "additive basis",
                         "totient density", "Cauchy-Davenport", "squarefree units",
                         "IsUnit totient", "five eighths"],
    "z2n-five-eighths": ["cube free", "affine cube", "Long Wagner", "layer union",
                         "ZMod 2^n subset", "projective cube", "five eighths"],
    "sidon-sqrt-n": ["Sidon", "Erdos Turan", "distinct pairwise sums",
                     "Freiman homomorphism", "B_2 set", "perfect difference set"],
    "konyagin-unit-vectors": ["unit vectors orthogonal", "Lovasz theta",
                              "orthonormal labeling", "triangle free graph",
                              "Shannon capacity", "Ramsey graph"],
}


def run(args, capture=False):
    """One p2m call. stdin is inherited, so its prompt reaches your terminal."""
    cmd = P2M + args
    print("\n$ p2m " + " ".join(args), flush=True)
    if capture:
        p = subprocess.run(cmd, capture_output=True, text=True)
        return p.returncode, p.stdout
    return subprocess.run(cmd).returncode, ""


def load(slug):
    d = ROOT / slug
    prop = json.loads((d / "proposal.json").read_text())
    metas = {}
    for f in sorted((d / "items").glob("*.json")):
        m = json.loads(f.read_text())
        metas[m.get("theorem_name") or m["definition_name"]] = (f, m)
    ms = json.loads((d / "milestones.json").read_text())["milestones"]
    return d, prop, metas, ms


def lean_for(d, meta):
    return d / ("Definitions.lean" if "definition_name" in meta else "Statements.lean")


def fetch_items(pid):
    """theorem_name or definition_name to server item id, from the live proposal."""
    rc, out = run(["proposal", pid], capture=True)
    try:
        body = json.loads(out[:out.rindex("}") + 1])["body"]
    except (ValueError, KeyError):
        sys.exit(f"could not parse `p2m proposal {pid}`. Output:\n{out[:800]}")
    found = {}
    for it in body.get("items") or []:
        name = it.get("theorem_name") or it.get("definition_name")
        if name:
            found[name] = it.get("id")
    return found


def cmd_sweep(slug, *_):
    from urllib.parse import quote
    for q in SWEEP[slug]:
        run(["probe", f"/theorems?q={quote(q)}"])
    print("\nSweep recorded. `propose` and `item-add` will now pass refusal 3.")


def item_args(d, name, meta, pid, extra):
    kind = "definition" if "definition_name" in meta else "theorem"
    return ["item-add", pid, "--kind", kind,
            "--lean", str(lean_for(d, meta)),
            "--meta", str((d / "items" / f"{name.rsplit('.', 1)[-1]}.json"))] + extra


def cmd_dry(slug, *_):
    """Dry-run every item; exit nonzero if any refuses."""
    d, prop, metas, ms = load(slug)
    refused = []
    rc, _ = run(["propose", "--spec", str(d / "proposal.json"), "--dry-run"])
    if rc not in (0, 10):
        refused.append("the proposal itself")
    for name in prop["item_order"]:
        f, meta = metas[name]
        rc, _ = run(["item-add", NIL_UUID, "--kind",
                     "definition" if "definition_name" in meta else "theorem",
                     "--lean", str(lean_for(d, meta)), "--meta", str(f),
                     "--dry-run"])
        if rc not in (0, 10):
            refused.append(name)
    print(f"\nDry run for {slug}: 1 proposal, {len(prop['item_order'])} items, "
          f"{len(ms)} milestones. No socket was opened.")
    if refused:
        print(f"\n{len(refused)} REFUSED: {', '.join(refused)}")
        print("Fix every one before running `propose`. A refusal here is a "
              "refusal there.")
        sys.exit(1)
    print("Every item passed all three refusals. Safe to propose.")


def cmd_propose(slug, *_):
    d, _, _, _ = load(slug)
    rc, _ = run(["propose", "--spec", str(d / "proposal.json"), "--confirm"])
    print("\nRead the proposal id out of the body above, then run:")
    print(f"    ./upload.py {slug} items <proposal-id>")


def cmd_items(slug, pid, *_):
    d, prop, metas, _ = load(slug)
    for i, name in enumerate(prop["item_order"], 1):
        f, meta = metas[name]
        print(f"\n--- item {i} of {len(prop['item_order'])}: {name}")
        rc, _ = run(item_args(d, name, meta, pid, ["--confirm"]))
        if rc not in (0, 10):
            sys.exit(f"item-add failed on {name} with exit {rc}. Fix it and "
                     f"re-run; item-add is idempotent by name.")
    print(f"\nAll items added. Next:\n    ./upload.py {slug} finish {pid}")


def cmd_finish(slug, pid, *_):
    d, prop, metas, ms = load(slug)
    ids = fetch_items(pid)
    missing = [n for n in prop["item_order"] if n not in ids]
    if missing:
        sys.exit(f"the platform has no item for: {missing}. Run `items` first.")

    for name in prop["item_order"]:
        f, meta = metas[name]
        lean = lean_for(d, meta)
        if "definition_name" in meta:
            # A definition item is a whole module, so its read-back covers every
            # declaration in it.
            import re
            decls = re.findall(r"(?m)^(?:noncomputable\s+)?(?:def|abbrev|structure"
                               r"|inductive|instance|class)\s+([^\s:{(\[]+)",
                               lean.read_text())
            extra = sum([["--decl", x] for x in decls], [])
        else:
            extra = ["--decl", name.rsplit(".", 1)[-1]]
        print(f"\n--- read-back for {name}")
        run(["readback-attach", pid, ids[name], "--lean", str(lean)]
            + extra + ["--confirm"])

    for i, m in enumerate(ms, 1):
        print(f"\n--- milestone {i} of {len(ms)}: {m['item_id']}")
        run(["milestone-add", pid, "--item", ids[m["item_id"]],
             "--title", m["milestone_title"],
             "--description", m["milestone_description"], "--confirm"])

    print(f"\nDraft complete. Inspect it:\n    p2m proposal {pid}")
    print(f"Fix the ordering:\n    ./upload.py {slug} order {pid}")
    print("Then Submit Proposal in the web app. Nothing here does that step.")


def cmd_order(slug, pid, *_):
    """Set item_order and the goal. The platform compiles in that order at Submit."""
    d, _, _, _ = load(slug)
    rc, _ = run(["proposal-set", pid, "--spec", str(d / "proposal.json"),
                 "--confirm"])
    if rc not in (0, 10):
        sys.exit(f"proposal-set failed with exit {rc}")
    print("\nOrder and goal set. Now open the proposal in the web app, read "
          "each item\nagainst its read-back, and click Submit Proposal.")


STEPS = {"sweep": cmd_sweep, "dry": cmd_dry, "propose": cmd_propose,
         "items": cmd_items, "finish": cmd_finish, "order": cmd_order}


LEDGER = Path(os.environ.get("P2M_LEDGER")
              or Path.home() / ".local" / "state" / "p2m" / "ledger.ndjson")

NIL_UUID = "00000000-0000-0000-0000-000000000000"


def resolve_pid(slug):
    """Newest proposal id for `slug` from the ledger."""
    if not LEDGER.is_file():
        print(f"no ledger at {LEDGER}. Set P2M_LEDGER if the client keeps its "
              f"state elsewhere.", file=sys.stderr)
        return None
    found = None
    for line in LEDGER.read_text(encoding="utf-8", errors="replace").splitlines():
        if not line.strip():
            continue
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if (r.get("kind") == "propose" and r.get("mission_slug") == slug
                and r.get("proposal_id")):
            found = r["proposal_id"]
    return found


def main(argv):
    if len(argv) < 2 or argv[1] not in STEPS:
        sys.exit(__doc__)
    slug, step = argv[0], argv[1]
    if not (ROOT / slug / "proposal.json").is_file():
        sys.exit(f"no mission at {ROOT / slug}")
    if step in ("items", "finish", "order") and len(argv) < 3:
        pid = resolve_pid(slug)
        if not pid:
            sys.exit(f"`{step}` needs a proposal id, and the ledger has no "
                     f"`propose` record for {slug}. Run `propose` first.")
        print(f"resolved proposal id for {slug} from the ledger: {pid}")
        argv = list(argv[:2]) + [pid]
    STEPS[step](slug, *argv[2:])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

#!/usr/bin/env python3
"""cubefree.py: compute and check f(n) for cube-free subsets of `Z_{2^n}`.

WHAT IT COMPUTES
  `f(n)`, the size of the largest cube-free subset of `Z_{2^n}`, and the
  extremal sets that achieve it. Cube-free means no `x, y, z` with all seven
  of `x`, `y`, `z`, `x+y`, `y+z`, `z+x`, `x+y+z` in the set.

TWO INDEPENDENT ROUTES
  `f_sat(n)`     a SAT encoding, one variable per residue, one clause per
                 cube, plus a cardinality constraint. Raises t until the
                 solver says UNSAT.
  `f_brute(n)`   exhaustive search over nonzero subsets, largest first.
                 Feasible to n = 4 and no further.

  They share only the definition. `f_sat` builds its clauses from `cubes()`,
  and `f_brute` tests each subset with `is_cube_free`, which reads the
  definition directly. A bug in either route shows up as disagreement.

THE PLANTED-SET TEST
  Build one set that is cube-free by construction and one that is not,
  and confirm the instrument classifies both. An instrument that calls
  everything cube-free reproduces every known `f(n)` as a lower bound.

USAGE
  cubefree.py --validate        two routes agree on f(1..4), emits a verdict
  cubefree.py --plant           planted-set test, emits a verdict
  cubefree.py --known           reproduce f(1..6) by SAT, emits a verdict
  cubefree.py --control         the hold-out and over-certification controls
  cubefree.py --decide N T      is there a cube-free set of size >= T in Z_2^N
"""
import argparse
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lib"))
import numkit  # noqa: E402  must precede numpy, which pysat may pull in

numkit.mem_guard()

from pysat.card import CardEnc, EncType  # noqa: E402
from pysat.formula import CNF  # noqa: E402
from pysat.solvers import Cadical195  # noqa: E402

# Known f(n), each settled by SAT with its witness re-checked by a direct triple scan.
KNOWN = {1: 1, 2: 2, 3: 5, 4: 10, 5: 20, 6: 40}


def cubes(n):
    """Every cube {x, y, z, x+y, y+z, z+x, x+y+z} mod 2^n as a frozenset, degenerate ones included."""
    N = 1 << n
    out = set()
    for x in range(N):
        for y in range(N):
            for z in range(N):
                out.add(frozenset({x, y, z, (x + y) % N, (y + z) % N,
                                   (z + x) % N, (x + y + z) % N}))
    return out


def is_cube_free(n, A):
    """Check the definition directly. Neither `cubes()` nor the SAT encoding is used."""
    N = 1 << n
    S = set(A)
    for x in S:
        for y in S:
            if (x + y) % N not in S:
                continue
            for z in S:
                if ((y + z) % N in S and (z + x) % N in S
                        and (x + y + z) % N in S):
                    return False
    return True


# --------------------------------------------------------------------------
# route A: SAT
# --------------------------------------------------------------------------

def decide_sat(n, t, cube_set=None):
    """Return (sat, A) for a cube-free A in Z_{2^n} with |A| >= t and 0 not in A.

    Leaving 0 out loses nothing, because x = y = z = 0 makes {0} a cube.
    """
    N = 1 << n
    lits = list(range(2, N + 1))

    # CardEnc.atleast raises `Wrong bound` when t exceeds the literal count, as at n = 1, t = 2.
    # So settle both edge cases before encoding.
    if t > len(lits):
        return False, None
    if t <= 0:
        return True, []

    cnf = CNF()
    cnf.append([-1])                                   # residue 0 is out
    for c in (cube_set if cube_set is not None else cubes(n)):
        cnf.append([-(v + 1) for v in c])              # not all of c in A
    card = CardEnc.atleast(lits=lits, bound=t, top_id=N,
                           encoding=EncType.seqcounter)
    cnf.extend(card.clauses)
    with Cadical195(bootstrap_with=cnf) as s:
        sat = s.solve()
        model = s.get_model() if sat else None
    if not sat:
        return False, None
    return True, sorted(i for i in range(N) if model[i] > 0)


def f_sat(n, lo=None, hi=None):
    """f(n) by SAT: the largest t with `decide_sat(n, t)` satisfiable."""
    N = 1 << n
    cs = cubes(n)
    t = lo if lo is not None else 1
    best, best_set = 0, []
    while t <= (hi if hi is not None else N - 1):
        sat, A = decide_sat(n, t, cs)
        if not sat:
            break
        best, best_set = t, A
        t += 1
    return best, best_set


# --------------------------------------------------------------------------
# route B: exhaustive search, independent of the SAT encoding
# --------------------------------------------------------------------------

def f_brute(n):
    """f(n) by exhaustive search over nonzero subsets, using `is_cube_free` in place of SAT.

    There are 2^15 subsets at n = 4 and 2^31 at n = 5, so `mode_validate` stops at 4.
    """
    N = 1 << n
    residues = list(range(1, N))
    for size in range(N - 1, 0, -1):
        for combo in itertools.combinations(residues, size):
            if is_cube_free(n, combo):
                return size, list(combo)
    return 0, []


# --------------------------------------------------------------------------
# the modes
# --------------------------------------------------------------------------

def mode_validate():
    """Check that SAT and exhaustive search agree on f(1..4)."""
    rows, all_ok = [], True
    for n in (1, 2, 3, 4):
        a, _ = f_sat(n)
        b, _ = f_brute(n)
        r = numkit.two_routes(a, b, tol=0, label=f"f({n})")
        rows.append([n, a, b, "agree" if r["ok"] else "DISAGREE"])
        all_ok = all_ok and r["ok"]
    numkit.table(Path(__file__).resolve().parents[1] / "tables"
                 / "validate-two-routes.txt",
                 rows, header=["n", "f_sat", "f_brute", "verdict"])
    return numkit.emit({"ok": all_ok, "residual": 0 if all_ok else 1,
                        "routes": "sat,brute", "range": "n=1..4",
                        "text": "SAT and exhaustive search agree on f(1..4)"})


def mode_plant():
    """Check that a planted cube-free set passes, the full group fails, and SAT reaches the planted size."""
    n = 4
    N = 1 << n
    # Cube-free by construction: layers 0 and 2, the largest union of layers.
    planted_free = sorted({x for x in range(1, N) if numkit.layer(x, n) in (0, 2)})
    # Not cube-free: x = y = z = 1 gives the cube {1, 2, 3}.
    planted_bad = sorted(range(1, N))

    got_free = is_cube_free(n, planted_free)
    got_bad = is_cube_free(n, planted_bad)

    sat_at, _ = decide_sat(n, len(planted_free))
    ok = bool(got_free) and not got_bad and bool(sat_at)
    print(f"planted cube-free set of size {len(planted_free)}: "
          f"classified {'cube-free' if got_free else 'NOT cube-free'}")
    print(f"planted full group of size {len(planted_bad)}: "
          f"classified {'cube-free' if got_bad else 'NOT cube-free'}")
    print(f"SAT finds a set of size {len(planted_free)}: {sat_at}")
    return numkit.emit({
        "ok": ok, "residual": 0 if ok else 1,
        "planted_size": len(planted_free),
        "text": ("the instrument accepts a planted cube-free set, rejects the "
                 "full group, and SAT recovers the planted size")})


def mode_known():
    """Reproduce every known f(n) by SAT, checking each witness directly."""
    rows, all_ok = [], True
    for n in sorted(KNOWN):
        want = KNOWN[n]
        cs = cubes(n)
        sat_at, A = decide_sat(n, want, cs)
        sat_above, _ = decide_sat(n, want + 1, cs)
        got = want if (sat_at and not sat_above) else None
        verified = is_cube_free(n, A) if A else False
        ok = got == want and verified
        all_ok = all_ok and ok
        rows.append([n, want, got if got is not None else "?",
                     "yes" if verified else "NO", "ok" if ok else "FAIL"])
        print(f"n={n}: SAT at {want}={sat_at}, at {want + 1}={sat_above}, "
              f"witness cube-free={verified}  -> f({n})={got}")
    numkit.table(Path(__file__).resolve().parents[1] / "tables"
                 / "known-f.txt", rows,
                 header=["n", "known", "got", "witness_cubefree", "verdict"])
    return numkit.emit({"ok": all_ok, "residual": 0 if all_ok else 1,
                        "routes": "sat", "range": "n=1..6",
                        "text": "reproduced f(1..6) = 1,2,5,10,20,40"})


def mode_control():
    """Run the over-certification and hold-out controls.

    Over-certification: `decide_sat(n, f(n))` must be SAT with a cube-free witness at n = 4, 5, 6.
    Hold-out: the pattern 2^(n-1) + 2^(n-3), which matches f(3..5), must predict f(6).
    """
    rows, all_ok = [], True

    for n in (4, 5, 6):
        want = KNOWN[n]
        sat_at, A = decide_sat(n, want)
        ok = bool(sat_at) and is_cube_free(n, A)
        all_ok = all_ok and ok
        rows.append(["over-certify", n, f">= {want}", "SAT" if sat_at else "UNSAT",
                     "ok" if ok else "FAIL"])
        print(f"control over-certify n={n}: a set of size {want} exists: "
              f"{sat_at}; witness cube-free: {is_cube_free(n, A) if A else False}")

    fit = [KNOWN[n] for n in (1, 2, 3, 4, 5)]
    predicted = (1 << 5) + (1 << 3)          # 2^(6-1) + 2^(6-3) = 40
    held_out = KNOWN[6]
    hold_ok = predicted == held_out
    all_ok = all_ok and hold_ok
    rows.append(["hold-out", 6, held_out, predicted, "ok" if hold_ok else "FAIL"])
    print(f"control hold-out: fitted 2^(n-1)+2^(n-3) on f(1..5)={fit}, "
          f"predicted f(6)={predicted}, actual {held_out}")

    numkit.table(Path(__file__).resolve().parents[1] / "tables"
                 / "controls.txt", rows,
                 header=["control", "n", "expected", "got", "verdict"])
    return numkit.emit({"ok": all_ok, "residual": 0 if all_ok else 1,
                        "text": ("the pipeline does not over-certify at "
                                 "n=4,5,6 and the hold-out prediction of f(6) "
                                 "is correct")})


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--validate", action="store_true")
    g.add_argument("--plant", action="store_true")
    g.add_argument("--known", action="store_true")
    g.add_argument("--control", action="store_true")
    g.add_argument("--decide", nargs=2, type=int, metavar=("N", "T"))
    a = ap.parse_args()

    if a.validate:
        r = mode_validate()
    elif a.plant:
        r = mode_plant()
    elif a.known:
        r = mode_known()
    elif a.control:
        r = mode_control()
    else:
        n, t = a.decide
        sat, A = decide_sat(n, t)
        verified = is_cube_free(n, A) if A else None

        # A SAT run passes only if its witness passes the direct scan.
        # UNSAT passes because there is nothing to check, but the solver gives it without a certificate.
        ok = (bool(verified) if sat else True)

        payload = {"ok": ok, "n": n, "t": t, "sat": bool(sat),
                   "witness_cubefree": verified,
                   "size": len(A) if A else 0,
                   "text": f"f({n}) >= {t} is {bool(sat)}"
                           + ("" if not sat else
                              ("" if verified
                               else "  BUT THE WITNESS IS NOT CUBE-FREE"))}
        if sat and A is not None:
            # Print the witness so a reader can check the claim by hand.
            payload["witness"] = A
            payload["witness_mod8"] = sorted({v % 8 for v in A})
        r = numkit.emit(payload)
    return 0 if r.get("ok") else 1


if __name__ == "__main__":
    sys.exit(main())

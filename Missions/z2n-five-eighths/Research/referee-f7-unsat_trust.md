# Referee: claim f7, joint `unsat_trust`

Verdict: **UNCLEAR**.

## The step

Claim, Step 4/5:

> Cadical195, single thread, 10 GB address-space cap.
> `decide(7, 81)  ->  UNSAT   (27 minutes)`
> ... UNSAT at 81 gives `f(7) <= 80`.

Everything above `f(7) <= 80` rests on one unreplicated return value of
`s.solve()` inside `decide_sat`.

## What I attacked, and to what bound

All numerics via `python3`, pysat 1.9.dev15,
CaDiCaL 1.9.5 (the `.so` also contains 1.0.3, 1.5.3, 3.0.0, Kissat 4.0.4,
Glucose, Lingeling, Minisat, Mergesat).

### 1. Vacuously unsatisfiable cardinality encoding at large bounds. CLOSED.

Built `CardEnc.atleast(lits=list(range(2,129)), bound=81, top_id=128,
encoding=EncType.seqcounter)`, the exact call in `decide_sat(7, 81)`.

- 7487 clauses, aux vars 129..3854, so no collision with the 1..128 the cube
  clauses use. `top_id=N=128` is the right value.
- Standalone: SAT. Not vacuous.
- Boundary: fix all 127 literals by unit clauses to a set of size k and solve.
  Must be SAT iff k >= 81. 132 tests over k = 76..86, with prefix, suffix,
  stride-2 and random subsets. 0 mismatches.
- Exhaustive: for m = 1..10 literals, every bound 1..m, every one of the 2^m
  assignments, projection of the models equals exactly {|on| >= bound}. 0
  mismatches.

So the constraint is not over-strong at bound 81, and it is not the source of
the UNSAT.

### 2. The RLIMIT_AS cap presenting as UNSAT. CLOSED, and worse than the claim says.

`numkit.mem_guard()` caps `RLIMIT_AS`. Made CaDiCaL hit the cap (900k random
3-clauses, cap = VSZ + 40 MB, then bootstrap and solve):

    terminate called after throwing an instance of 'std::bad_alloc'
    Aborted (exit 134)

An allocation failure under the cap is a SIGABRT, and stdout stays empty. It
cannot present as UNSAT, because `numkit.emit` never runs. The log does contain
the JSON line, so the run did not hit the cap while solving.

Separately: the claim says "10 GB address-space cap". `numkit.mem_guard`
defaults to `NUMKIT_MEM_GB` or **8**, not 10. The claim states a number the
instrument does not set by default. That discrepancy does not change the
verdict, but the claim is describing a run configuration it does not
evidence.

### 3. UNKNOWN silently returned as UNSAT. CLOSED for signals.

`Cadical195.solve()` returns the raw C result; only `solve_limited` maps 0 to
`None`. So if the C layer ever returned UNKNOWN, `decide_sat` would read it as
UNSAT. Checked whether an interrupt can produce that: `nm -D -u` on
`pysolvers.cpython-311-x86_64-linux-gnu.so` does not list a
`PyErr_CheckSignals` import, and an empirical SIGINT delivered 4 s into a
2-minute PHP(12,11) solve was ignored outright. The plain `solve()` path leaves
the terminator unconnected and the budget unset, so UNKNOWN is unreachable.
This worry is closed.

### 4. Formula soundness (over-constraint), by inspection.

Every clause in the formula is implied by cube-freeness: `cubes(n)` emits
`{x,y,z,x+y,y+z,z+x,x+y+z}` for actual triples, so each clause is a genuine
"not all of a real cube". `[-1]` is sound by Step 1 and is in any case the
clause `cubes()` already emits for x=y=z=0. Combined with 1, every cube-free
A with |A| >= 81 extends to a model. So a correct UNSAT does entail
`f(7) <= 80`. The weight is entirely on the solver run, not the encoding.

### 5. NOT COMPLETED, so the verdict is not HOLDS.

Two experiments were cut off by the turn budget:

- Truncation check on the real formula. I never confirmed that the n=7,
  t=81 CNF that `decide_sat` hands to `Cadical195(bootstrap_with=cnf)` arrives
  intact, i.e. that `s.nof_clauses()` equals `len(cnf.clauses)` and
  `s.nof_vars()` equals `cnf.nv`. `cnf.extend(card.clauses)` and
  `append_formula` on a pysat 1.9.dev `CNF` object are the two places a clause
  set can be dropped, and 1.9.dev is a pre-release with the Formula refactor in
  flight. A *dropped cube clause* weakens the formula and cannot cause UNSAT,
  so the dangerous direction is narrow, but I did not close the worry.
- Multi-solver, multi-encoding agreement at n = 3..6. A cross-check over 9
  in-process solvers and 6 cardinality encodings on `f(n)+1` timed out before
  producing any row. So I cannot even report how far the corroboration the
  claim cites actually reaches under a different solver.

## The evidence question, stated plainly

The claim's own defense of the UNSAT side is "for every n in 1..6 it returned
SAT at f(n) and UNSAT at f(n)+1". Those instances have at most 63 free
variables and finish in well under a second. The n=7 instance has 127 free
variables plus ~3700 aux and ran 27 minutes. That is a difference of orders of
magnitude in search, and easy-instance agreement is nearly no evidence about a
long run: the failure modes that matter at 27 minutes (a clause-database
reduction bug, a chronological-backtracking bug, a vivification bug) are
exactly the ones that never fire on a formula solved in preprocessing.

The artifact is `tables/sat-n7-81.log`, 234 bytes, two lines. No conflicts,
decisions, propagations, wall time, peak memory, clause or variable count, hash
of the CNF, solver version string, or DRAT. Nobody can check any part of that
file. The verdict is not merely uncertified, it is unauditable without a
27-minute re-run. UNCLEAR exists for exactly this: the claim does not pin the
joint down well enough to attack the solver run itself.

## On the two facts supplied mid-task

**The SAT side being independently reproduced does not touch this joint.** A
verified 80-element witness proves `f(7) >= 80`. It is consistent with
`f(7) = 80`, `81`, `90` and `127`. It constrains the UNSAT run not at all,
beyond ruling out the trivial failure of a formula that is UNSAT at every
bound. The claim already knew that: it is why `unsat_trust` is a separate
joint.

**Long and Wagner's Gurobi check changes the prior, not the audit.** Say it
plainly: two unaudited computations agreeing is two unaudited computations
agreeing. What it does buy is real but narrow. An ILP under Gurobi does not
share code, an encoding, or a cardinality construction with pysat + CaDiCaL +
seqcounter, so a *bug* in one is unlikely to be mirrored in the other, and
independent agreement is decent evidence against solver error. What it does
not buy: it is not a check of *our* run, so it cannot distinguish "CaDiCaL
proved this formula unsatisfiable" from "our formula was not the one we think
we built". A modeling error on our side that makes the formula spuriously
UNSAT would still agree with Gurobi, because Gurobi is answering the
mathematical question and we would be answering a different one. And it
inherits their conjecture's implication chain: what they check is a conjecture
that *implies* f(7) <= 80, not f(7) <= 80 itself, so believing it means
believing that implication too, which this claim does not state or verify.

Net: external agreement makes "the mathematics is right" more likely and leaves
"this run computed the mathematics" exactly where it was. The campaign is
entitled to say f(7) = 80 is probably true. It is not yet entitled to say its
own UNSAT run is the reason.

## What would settle the question

Named only because the claim asks whether the verdict *may be believed*, not as
a repair: a DRAT proof from CaDiCaL checked by an independent checker, or the
same instance decided by Kissat 4.0.4 (present in the same `.so`, different
code base), or a log recording solver statistics and a hash of the CNF. None
exists. One re-run under a second solver is roughly 30 minutes and was out of
scope for this dispatch.

## Bound on this referee's effort

Four attack vectors run to completion (cardinality vacuity, memory cap,
UNKNOWN-as-UNSAT, formula over-constraint by inspection); two cut off
(truncation on the real n=7 CNF, multi-solver agreement at n<=6). n=7 was not
re-run, per dispatch.

# Referee: claim `f7`, joint `encoding` -- verdict HOLDS

Scope: Steps 1 to 3 of `claim-f7.md` only. Whether the CNF built by
`decide_sat(n, t)` is satisfiable exactly when a cube-free `A` in `Z_{2^n}`
with `|A| >= t` exists. Instrument: `instruments/cubefree.py`.

## The step I turned on

> **Step 2 (the encoding).** ... For every cube `C`, taken as the *set*
> `{x, y, z, x+y, y+z, z+x, x+y+z}` of its seven expressions, add the clause
> `NOT v_c1 OR NOT v_c2 OR ...` over the distinct elements of `C`.

and Step 3's

> So the formula is satisfiable exactly when a cube-free set of size at least
> `t` exists.

The joint's stated worry is that `cubes(n)` generates too few cubes.

## 1. Is `cubes(n)` the complete cube family?

From-scratch re-enumeration (my own triple loop, own code, own transcription),
compared as sets of frozensets:

    n=1  |cubes()|=2       indep=2       equal=True
    n=2  |cubes()|=9       indep=9       equal=True
    n=3  |cubes()|=78      indep=78      equal=True
    n=4  |cubes()|=668     indep=668     equal=True
    n=5  |cubes()|=5448    indep=5448    equal=True
    n=7  |cubes()|=349968  indep=349968  equal=True

Set equality in both directions, so no cube is missing and no clause is
spurious. Every element of `cubes(7)` is the image of an actual triple, by
construction of the independent generator; cube sizes present are 1..7, i.e.
the degenerate collapses are kept, as Step 2 says. 17368 of the 349968 cubes
contain residue 0.

This check has a real limit and I state it: my generator runs the same
`for x, y, z in Z_N^3` shape as the code's. It catches a transcription or
dedup bug, it does not independently certify that "all triples over `Z_N`" is
the right family. That part is a one-line reading of the definition. The
definition in the claim ("the triple ranges over all of `Z_N`, degenerate
choices allowed") matches the loop exactly.

Stronger, encoding-free evidence that the family is not too small is in
section 3: the clause set was checked against a direct triple scan that never
touches `cubes()`.

## 2. Ground truth for the whole formula, n = 1..4

Exhaustive search over **all** `2^N` subsets of `Z_N`, 0 allowed, cube-freeness
decided by a direct triple scan over all of `Z_N` written from the definition:

    n=1: true f = 1    n=2: true f = 2    n=3: true f = 5    n=4: true f = 10
    cube-free sets containing 0: 0 at every n  (Step 1 confirmed empirically)

For n<=3 the mask route and the direct triple scan agreed on all `2^N` subsets
(0 mismatches). Then, for every `t` from -1 to `N+1` inclusive,
`decide_sat(n, t)` agreed with `t <= f(n)`: no disagreement at any n, any t,
including the guarded edge cases `t <= 0` and `t > len(lits)`. Every SAT
witness returned had `len(A) >= t` and passed the direct scan.

So the whole Step 1 + Step 2 + Step 3 pipeline is exactly right, both
directions, wherever brute force can adjudicate it.

## 3. n = 7, the CNF's projection vs the definition

Built the exact CNF `decide_sat(7, t)` builds (`[-1]`, 349968 cube clauses,
`CardEnc.atleast(lits=2..128, bound=t, top_id=128, seqcounter)`) and tested it
under full assumptions on the 128 residue variables, against a fast
cube-checker (`A & rot(A,x) & rot(A,y) & rot(A,x+y) != 0`) that was first
validated against the slow triple scan on 40 random sets.

    layer-{0,2} set  {x : v2(x) in {0,2}} = {v : v mod 8 in {1,3,4,5,7}}
      size 80, cube-free by direct triple scan: True
    CNF(t=80) accepts it: True        (want True)
    CNF(t=81) accepts it: False       (want False, size 80)
    CNF(t=80) accepts it plus 0: False (want False)

That reproduces the published extremal construction independently of the
solver, so `f(7) >= 80` does not rest on the SAT run at all.

Then agreement testing of "CNF(t=81) accepts A" vs "A cube-free and |A| >= 81":

- all 47 one-element extensions of the 80-set to size 81: 0 disagreements
- 20000 random one-out-two-in swaps off the 80-set: 0 disagreements
- 5000 uniform random 81-subsets of `{1..127}`: 0 disagreements
- 127 translates and 64 unit-multiples of the 80-set, topped up to 81:
  0 disagreements

Total 25191 assignments of size >= 81 tested, 0 disagreements, 0 genuinely
cube-free 81-sets found. Every rejection by the formula was matched by a real
cube found by the direct scan, so at the exact `n` and `t` where the UNSAT
claim lives the formula is not rejecting for a spurious reason.

## 4. The cardinality constraint

- Exhaustive projection check: for n=3 (7 lits, all 128 assignments, every
  `t` in 1..7) and n=4 (15 lits, all 32768 assignments, every `t` in 1..15),
  the seqcounter `atleast` encoding is satisfiable under a fixed assignment
  exactly when popcount >= t. No over-constraint, no under-constraint.
- At the real n=7 parameters, `t` in {79,80,81,82,127}: aux variables occupy
  129..3920 without colliding with residue variables 1..128, and 60 random
  exact-size probes at each of six sizes straddling the bound gave 0
  mismatches against popcount >= t.

## 5. Cross-encoding replication

A second SAT pipeline I wrote from scratch, with the variable numbering
reversed (residue `v` -> variable `N - v`, so a numbering bug shows up as
disagreement) and its own cube enumeration, under four other cardinality
encodings:

    totalizer    f(1..6) = [1,2,5,10,20,40]
    mtotalizer   f(1..6) = [1,2,5,10,20,40]
    kmtotalizer  f(1..6) = [1,2,5,10,20,40]
    cardnetwrk   f(1..6) = [1,2,5,10,20,40]
    seqcounter   f(1..6) = [1,2,5,10,20,40]   (the instrument itself)

Each of these searched upward until the first UNSAT, so the UNSAT side is
exercised at `f(n)+1` for every n in 1..6 under five encodings.

## Verdict: HOLDS

I could not break the encoding. `cubes(n)` is complete against a
from-scratch enumeration at n=1..5 and n=7 with exact set equality in both
directions; the assembled formula matches exhaustive ground truth for every
`t` at n=1..4; the cardinality encoding's projection is exactly `popcount >= t`
by exhaustive check at n=3,4 and by probe at the real n=7 bounds; and across
25191 size->=81 assignments at n=7 the formula agreed with a direct triple scan
every time.

HOLDS is not correctness. Three things I did not close:

1. My independent cube enumerator shares the *shape* of the code's loop. It
   rules out a transcription bug, not a misreading of the definition. The
   claim's own definition and the loop do match, so any remaining error here
   is an error in the claim's definition relative to Long-Wagner, which is
   outside this joint.
2. The completeness direction at exactly `t = 81` is untestable head-on: no
   cube-free 81-set exists to feed it, so I could only test agreement on sets
   the definition already rejects. The argument that it is fine is structural
   (cube clauses and card clauses share only variables 1..128, both projections
   verified separately), not exhaustive.
3. This referee does not touch whether the solver's UNSAT answer is
   trustworthy. That is the `unsat_trust` joint and I did not enter it.

Scripts used: `/tmp/ref-enc/t_cubes.py`, `t_ground.py`, `t_card.py`,
`t_card7.py`, `t_n7.py`, `t_alt.py`, `t_hammer2.py`.

# Referee: claim `f7`, joint `witness`

Verdict: **HOLDS**.

Scope: only whether SAT at 80 exhibits a cube-free set of size 80 under the
definition stated in `claim-f7.md`. This referee does not address `encoding` or
`unsat_trust`, so it does not support the upper bound `f(7) <= 80`.

## The step turned on

Step 4 of the claim:

>     decide(7, 80)  ->  SAT     with a witness

and the joint's own worry:

> `is_cube_free` iterates `x, y, z` over the set `A` rather than over `Z_N`,
> so it could be checking a weaker condition than the definition above states.

Against the definition in the claim:

> A set `A` contained in `Z_N` is **cube-free** when there is no triple
> `(x, y, z)` of elements of `Z_N` with all seven of `x, y, z, x+y, y+z, z+x,
> x+y+z` lying in `A`. The triple ranges over all of `Z_N`, not over `A`.

## 1. Restricting the quantifier to A is a logical equivalence, proved then checked

The stated definition demands that **all seven** listed elements lie in `A`.
Three of the seven are `x`, `y`, `z` themselves. So any triple that witnesses a
cube already has `x, y, z` in `A`. Restricting the quantifier to `A` therefore
discards only triples that could not have witnessed anything. The `A`-quantified
condition and the `Z_N`-quantified condition are logically equivalent, not
merely equal on the sets tested.

`instruments/cubefree.py` lines 79-86 implement exactly the `A`-quantified form,
with a `continue` prune on `(x+y) % N not in S`. The prune is sound for the same
reason: `x+y` is one of the seven.

Confirmed empirically anyway, against a from-scratch reimplementation of the
literal claim-file wording (`x, y, z` looping over `range(N)`, all seven
memberships tested explicitly, degenerate triples included):

- `n = 1, 2, 3`: **all** `2^N` subsets (276 sets). 0 disagreements.
- `n = 4, 5`: 8000 uniform-random subsets. 0 disagreements.
- `n = 3, 4, 5`: 9000 further subsets drawn large (size in `[N/2, N-1]`,
  0 excluded), to hit the near-extremal regime. 0 disagreements.
- Non-vacuity of that last batch: `is_cube_free` returned True 388 times at
  `n = 3` and 10 times at `n = 4`, so the agreement is not "both always False".

## 2. Model-to-set extraction is right

`decide_sat` line 125: `sorted(i for i in range(N) if model[i] > 0)`.

Variable `v+1` encodes residue `v`; pysat's `get_model()` is a list whose index
`i` holds the literal of variable `i+1`. So `model[i] > 0` iff residue `i` is
selected. Checked directly: forcing residues `{1,2,5}` at `n = 3` and
`{3,7,11,15}` at `n = 4` by unit clauses and running the same extraction
returned exactly those sets. No off-by-one.

Auxiliary-variable collision was the other way this could go wrong: if the
sequential counter allocated variables inside `1..N`, the extraction would read
counter bits as residues and inflate the size. `CardEnc.atleast(..., top_id=N)`
allocates from `N+1` up. Verified at `n = 3, 5, 7`: lowest non-input variable is
`N+1` in every case (at `n = 7`, vars run to 3888, first aux is 129). No
collision, and `range(N)` cannot reach an aux variable.

`cnf.append([-1])` forces residue 0 out, so `0` is never in the extracted set.
Verified across every SAT call below.

## 3. The size counts what it should

End-to-end sweep, `n = 3, 4, 5, 6`, every `t` from 1 up to the first UNSAT:
for each SAT answer, checked `0 not in A`, `len(A) >= t`, and cube-freeness of
`A` under the literal `Z_N`-quantified checker. Every witness reached its
target size, excluded `0`, and was cube-free. First UNSAT landed at
`t = 6, 11, 21, 41`, i.e. at `f(n)+1` for the known values.

## 4. The n = 7 case, reproduced from scratch

    cubes(7): 349968 distinct cubes            (3.0 s)
    decide_sat(7, 80) -> SAT                   (156.8 s)
    |A| = 80          (exactly 80, not >= 80)
    0 in A: False     duplicates: none     all residues in 0..127
    literal-definition cube-free (x, y, z over ALL of Z_128): True   (2^21 triples)
    instrument is_cube_free: True

Witness:

    A = {1,3,4,5,7, 9,11,12,13,15, ..., 121,123,124,125,127}
      = { v in Z_128 : v mod 8 in {1,3,4,5,7} }

`/tmp/ref-witness/witness80.json` holds it; it reproduces from
`decide_sat(7, 80)` in under three minutes.

### Third route, independent of both checkers' code

The witness is the full preimage of `T = {1,3,4,5,7}` under the surjective
homomorphism `pi : Z_128 -> Z_8`. If `(x,y,z)` were a cube inside `pi^{-1}(T)`
then `(pi x, pi y, pi z)` is a cube inside `T`, since `pi` respects addition.
Exhaustive scan of all 512 triples in `Z_8^3` finds **0** cubes inside `T`.
Hence `A` is cube-free, by an argument that touches neither `is_cube_free` nor
`cubes()` nor the solver. `|T| = 5 = f(3)`, and `|A| = 16 * 5 = 80`.

### Non-degeneracy of the checkers at n = 7

Both checkers reject all 48 single-element extensions `A u {v}`, `v not in A`,
and agree with each other on all 48. So neither is a constant-True function at
`n = 7`, and the witness is maximal under single additions. (Consistency with
`f(7) = 80`, not evidence for the upper bound.)

## 5. Robustness to the one definitional ambiguity I could find

The claim admits degenerate triples (`x = y`, etc.). The Long-Wagner setting
may or may not. This does not touch the witness: allowing degenerate triples is
the **stronger** requirement, so a set cube-free under the claim's reading is a
fortiori cube-free under any reading that drops degenerate triples. The lower
bound `f(7) >= 80` survives either convention. The upper bound would not, but
that is the `encoding` joint.

## What I could not break, and two things worth naming anyway

I could not break this joint. Attacked to the bounds above: exhaustive at
`n <= 3`, 17k random subsets at `n <= 5`, every `t` at `n <= 6`, and a full
independent reproduction plus two extra routes at `n = 7`.

Two reporting weaknesses that are not breaks:

1. The claim file never prints the witness. Step 4 says "SAT with a
   witness" and stops. A referee cannot check the witness from the claim alone;
   I had to re-derive it. Reproduction succeeded, so the substance is fine, but
   the claim as written is not self-checking on its own strongest evidence.
2. `--decide` mode hardcodes `"ok": True` (line 305), independent of
   `witness_cubefree`. A run whose witness failed the direct check would still
   exit 0 and read as success. The failure would appear only in the
   `witness_cubefree` field of the payload, which nothing forces a reader to
   consult. The claim's Step 4 rests on that field having been read.

## Commands

Scripts in `/tmp/ref-witness/`: `indep.py` (literal-definition checker),
`t1.py`, `t2.py` (checker equivalence), `t3.py` (indexing and aux vars),
`t4.py` (`n = 3..6` end-to-end), `t7.py` (`n = 7`, `t = 80`), `t8.py` (quotient
route and single-element extensions). All run under
`PYTHONPATH=lib python3`.

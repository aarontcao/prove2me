# Next action for z2n-five-eighths

next: ask the human whether to install a DRAT checker, then certify the f(7) UNSAT

why: `f(7) = 80` is reproduced and refereed, and the `unsat_trust` joint's UNCLEAR is the only thing keeping the verdict at PARTIAL. That referee ruled out every mechanical failure it could test, but `tables/sat-n7-81.log` lacks a conflict count, a clause count, and a proof.

`pysat` can already emit DRAT with `Cadical195(..., with_proof=True)` plus `get_proof()`, so the pipeline only needs a checker. Expect the check to outlast the solve, so run it as a detached background job. Validate the pipeline first at `n = 6, t = 41`, where UNSAT is known.

## After that

The real gap is untouched. The bench traced the `2/3` chain's slack, exactly `2^n/24`, to a missing interaction between layer pairs `(1,2)` and `(5,6)`.

The extremal set at `n = 7` is `{v : v mod 8 in {1,3,4,5,7}}`. It's the preimage of `T = {1,3,4,5,7}`, which is cube-free in `Z_8`. The `5/8` constant is just `|T|/8` if every extremal set is such a preimage. The instrument can test this. Get several distinct extremal sets at `n = 5` and `n = 6`, and check that each one is a preimage of a subset of `Z_8`.

## Do not

Don't re-derive the dead ends in `inherit.md`. Don't treat `f(7) = 80` or the `2/3` bound as new. Long and Wagner's Gurobi check implies the first, and Meng 2026 calls the second trivial. Don't raise the verdict above PARTIAL while `unsat_trust` is UNCLEAR.

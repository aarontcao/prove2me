/-!
# Problems, library root. Not a build target, and that is the point.

The `Problems` library declares `globs = ["Problems.+"]`. That is
`Glob.submodules`, which matches every submodule of `Problems` and excludes
`Problems` itself. So this file is never elaborated by any build, and nothing
can make it a dependency of one.

It exists to carry the rule, next to the tree the rule is about.

## One directory per target

    Problems/<Ns>/<slug>/Solution.lean      our proof, and the only gated file
    Problems/<Ns>/<slug>/explanation.md     the prose sent with the submission
    Problems/<Ns>/<slug>/meta.json          non-secret provenance
    Problems/<Ns>/<slug>/ledger.md          only when a proof spans many turns

`<Ns>` and `<slug>` are the platform's `theorem_name` split on its last dot, so
`BSS.quadratic_system_equiv_single_quartic` gives `BSS` and
`quadratic_system_equiv_single_quartic`. Ask `p2m paths <theorem-id>` rather
than deriving it by hand.

## The two rules that make the layout mean something

**The basename `Solution.lean` is load bearing.** The gate policy grants the
full contract to `Problems/**/Solution.lean` and to nothing else. A
`helper.lean` beside a solution is skipped by the gate and refused by the
PreToolUse guard, so a proof that leans on one would pass a gate that never
read it. Put everything the proof needs in `Solution.lean`.

**`theorem solution` is the declaration the platform resolves.** It must be at
top level and it must be the only top-level theorem in the file. A namespace
counts as a different name. `p2m submit` refuses before posting, because a
submission is immutable and one spent on packaging is permanent.
-/

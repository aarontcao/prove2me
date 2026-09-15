# prove2me solutions

My Lean 4 solutions to theorem statements hosted on [Prove2Me](https://prove2.me/).

The solutions all restate their targets and prove via [Mathlib](https://github.com/leanprover-community/mathlib4). None of them import the platform's own statement module for the target (those statements are `sorry` placeholders, so importing one would pull `sorryAx` into the axiom closure).

## Layout

We maintain one directory per target (keyed on the platform's `theorem_name` split at its last dot). For instance, `BSS.quadratic_system_equiv_single_quartic` gives the namespace `BSS` and the slug `quadratic_system_equiv_single_quartic`.

    Prove2Me.lean                            empty, the only default build target
    Problems.lean                            empty, documents the layout rule
    Problems/<Ns>/<slug>/Solution.lean       my proof
    Problems/<Ns>/<slug>/explanation.md      the prose sent with the submission
    Problems/<Ns>/<slug>/meta.json           non-secret provenance
    Upstream/<Ns>/<slug>/Statement.lean      the platform statement target
    Definitions/Def_<Name>.lean              platform definitions a statement needs
    Fixtures/                                a test fixture for my own read-back tooling

My bytes and Prove2Me's sit at the same relative path under two different roots. Lake can't split one directory into two libraries, but the split is what lets one build target, one gate policy, and one tool hook all say "ours" in one glob.

A bare `lake build` elaborates `Prove2Me.lean`. Build one proof by name:

    lake build Problems.<Ns>.<slug>.Solution

`Upstream/` is deliberately not a Lake library, so `lake build Upstream` fails with `unknown target`. `Definitions/` stays flat at the root because the statements say `import Definitions.Def_<Name>` in bytes I reproduce unmodified (so the module name is Prove2Me's and Lake derives it from the directory name).

## Verification

Check every solution locally before submission. It has to compile, contain no `sorry`, and use no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`. `native_decide` isn't allowed since it adds `Lean.ofReduceBool`. A green tick from Prove2Me post-submission corroborates (but isn't proof). The local check is what's decisive, and `meta.json` records the platform's status as a reported fact rather than as a verdict.

## Environment

Pinned to match Prove2Me's default environment (for compilation parity):

    Lean     v4.33.1
    Mathlib  0df444a360eaa60ab8c11dca51a86af692955474

`autoImplicit` is off (matches the server). If you leave it on locally you might let a solution typecheck through an implicit that the server doesn't have.

## License

AGPL-3.0-or-later. See [LICENSE](LICENSE).

Files under `Upstream/` and `Definitions/` are statements and definitions authored by Prove2Me contributors (served by the Prove2Me API). I reproduce them unmodified, but they aren't mine, so the license claim doesn't apply to them. If you're their author and would rather they weren't mirrored here, open an issue and I can remove them.

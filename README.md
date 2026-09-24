# prove2me

Lean 4 solutions to [Prove2Me](https://prove2.me/) theorem statements, and
mission proposals of my own. Solutions restate their targets and prove them
through [Mathlib](https://github.com/leanprover-community/mathlib4); missions
contain goal theorems, definitions, and milestone chains with every statement
ending in `:= by sorry`.

## Layout

    Prove2Me.lean                            empty, the only default build target
    Problems.lean                            documents the layout rule
    Problems/<Ns>/<slug>/Solution.lean       my proof
    Problems/<Ns>/<slug>/explanation.md      the prose sent with the submission
    Problems/<Ns>/<slug>/meta.json           non-secret provenance
    Upstream/<Ns>/<slug>/Statement.lean      the platform statement target
    Definitions/Def_<Name>.lean              platform definitions a statement needs
    Missions/<slug>/                         mission proposals; see Missions/README.md

A bare `lake build` elaborates `Prove2Me.lean`, which is empty. Build one proof
by name:

    lake build Problems.<Ns>.<slug>.Solution

## Environment

Pinned to match Prove2Me's default environment:

    Lean     v4.33.1
    Mathlib  0df444a360eaa60ab8c11dca51a86af692955474

`autoImplicit` is off, which is the server's setting.

## License

AGPL-3.0-or-later. See [LICENSE](LICENSE).

Files under `Upstream/` and `Definitions/` are authored by Prove2Me
contributors and served by the Prove2Me API; I reproduce them unmodified, and
the license claim above does not extend to them.

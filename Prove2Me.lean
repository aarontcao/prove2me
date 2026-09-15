/-!
# prove2me, root module

This module is the only thing `lake build` builds by default. It is empty on
purpose, and it must stay empty.

`defaultTargets = ["Root"]` in `lakefile.toml` names a library whose only root
is this file and which declares no `globs`. Lake defaults `globs` to
`roots.map Glob.one`, and `Glob.one` selects exactly the one module without
reading the directory, so a bare `lake build` elaborates this file and nothing
else.

That was not true before 2026-09-14. The default target was the `Solutions`
library, whose `globs = ["Solutions.+"]` is `Glob.submodules`: it matches every
submodule and excludes the root. So a bare `lake build` elaborated every
solution and skipped the very file whose docstring claimed it was the only
thing built. At three solutions that was slow. At a thousand it is unusable.

Each target lives in its own directory and is built by name:

    lake build Problems.<Ns>.<slug>.Solution

Do not add imports here. An import of a solution would pull that file into the
default target. An import of anything under `Upstream/` or `Definitions/` would
pull an admitted third-party statement into it, and importing an `Upstream`
statement also pulls its `sorry` into the axiom closure. Those files are
elaborated only when `p2m admit` decides to, under an explicit audit mode.

The gate policy grants `gate` to `Problems/**/Solution.lean` and nothing else
in this tree. Our bytes get the full contract. Their bytes get no elaboration
at all unless something deliberate asks for it.
-/

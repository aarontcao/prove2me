/-!
# Problems

Library root for solved targets. Not itself a build target.

    Problems/<Ns>/<slug>/Solution.lean      our proof, the only gated file
    Problems/<Ns>/<slug>/explanation.md     prose sent with the submission
    Problems/<Ns>/<slug>/meta.json          non-secret provenance

`<Ns>` and `<slug>` come from the platform's `theorem_name` split on its last
dot. The platform resolves `theorem solution` at top level, so the declaration
must use that exact name, outside any namespace.
-/

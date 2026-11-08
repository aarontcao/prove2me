/-!
Library root for solved targets, not itself a build target. Each lives at
`Problems/<Ns>/<slug>/Solution.lean`, from `theorem_name` split on its last
dot, and must declare a top-level `theorem solution`.
-/

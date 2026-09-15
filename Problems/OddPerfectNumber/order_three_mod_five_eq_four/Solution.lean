import Mathlib

/-!
# Solution: the multiplicative order of 3 in `ZMod 5` is 4

The statement is restated here rather than imported. Importing
`Upstream.OddPerfectNumber.order_three_mod_five_eq_four.Statement` would pull
its `sorry` into this file's axiom closure, which is the reduction path this
integration refuses.

`ZMod 5` is a finite type with decidable equality, so every concrete power of
3 in it is decidable. `orderOf` itself is not. It is defined through an
`IsOfFinOrder` existential, so a bare `decide` gets stuck: the kernel reports
that `instDecidableEqNat (orderOf 3) 4` does not reduce. `decide +kernel` gets
stuck in the same place, because the obstruction is the definition and not the
reduction engine.

`orderOf_eq_iff` is the bridge. It rewrites the goal into two pieces that ARE
decidable: `3 ^ 4 = 1`, and no smaller positive exponent gives 1. The second
piece is a bounded quantifier, so `interval_cases` turns it into the three
concrete goals `3 ≠ 1`, `3 ^ 2 ≠ 1` and `3 ^ 3 ≠ 1`, each of which `decide`
closes by computing in `ZMod 5`.

Every `decide` here is the kernel one. `native_decide` would add
`Lean.ofReduceBool` to the axiom closure and fail the gate.
-/

-- The platform looks up a declaration named exactly `solution`, at top
-- level. A namespaced or differently named theorem returns WA with
-- "Unknown identifier `solution`", which costs a submission to discover.
theorem solution : orderOf (3 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

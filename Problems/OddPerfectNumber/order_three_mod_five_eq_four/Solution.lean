import Mathlib

/-!
The multiplicative order of 3 in `ZMod 5` is 4. Statement restated here to
avoid importing the `sorry`. Uses `orderOf_eq_iff` because `orderOf` itself
does not reduce under `decide`.
-/

-- The platform looks up a declaration named exactly `solution`, at top
-- level. A namespaced or differently named theorem returns WA with
-- "Unknown identifier `solution`", which costs a submission to discover.
theorem solution : orderOf (3 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

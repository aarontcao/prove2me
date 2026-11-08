import Mathlib

/-!
The multiplicative order of 3 in `ZMod 5` is 4, restated so we don't import the
`sorry`. `orderOf` doesn't reduce under `decide`, so we use `orderOf_eq_iff`.
-/

-- The platform wants a top-level theorem named exactly `solution`.
theorem solution : orderOf (3 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

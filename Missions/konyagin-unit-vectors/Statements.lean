import Mathlib

open scoped RealInnerProductSpace

/-!
Draft mission items for Konyagin's bound on triangle-free unit vector systems,
each ending in `:= by sorry`. Upper bound and Alon's matching lower bound.
-/

namespace KonyaginUnitVectors

/-- Upper bound: `‖∑ u_i‖ ≤ C n^(2/3)` for triangle-free unit vector systems. -/
theorem sum_norm_le_of_triangle_free :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) (u : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖u i‖ = 1) →
      (∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
        ⟪u i, u j⟫ = 0 ∨ ⟪u j, u k⟫ = 0 ∨ ⟪u i, u k⟫ = 0) →
      ‖∑ i, u i‖ ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by sorry

/-- Lower bound: `c n^(2/3) ≤ ‖∑ u_i‖` for every `n` (Alon). -/
theorem exists_sum_norm_ge_of_triangle_free_forall_n :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      ∃ (d : ℕ) (u : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, ‖u i‖ = 1) ∧
        (∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
          ⟪u i, u j⟫ = 0 ∨ ⟪u j, u k⟫ = 0 ∨ ⟪u i, u k⟫ = 0) ∧
        c * (n : ℝ) ^ ((2 : ℝ) / 3) ≤ ‖∑ i, u i‖ := by sorry

end KonyaginUnitVectors

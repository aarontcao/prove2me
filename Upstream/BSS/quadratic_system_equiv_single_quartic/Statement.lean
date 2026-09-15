import Mathlib

namespace BSS

theorem quadratic_system_equiv_single_quartic {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ i, (p i).totalDegree ≤ 2) :
    ∃ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ 4 ∧
      ∀ x : Fin n → ℝ,
        (MvPolynomial.eval x f = 0 ↔ ∀ i, MvPolynomial.eval x (p i) = 0) := by sorry

end BSS

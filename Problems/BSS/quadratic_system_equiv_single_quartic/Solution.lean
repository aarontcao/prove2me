import Mathlib

/-!
A real quadratic system is equivalent to a single quartic equation. The witness
is the sum of squares. Statement restated here to avoid importing the `sorry`.
-/

open MvPolynomial

-- The platform looks up a declaration named exactly `solution`, at top
-- level. A namespaced or differently named theorem returns WA with
-- "Unknown identifier `solution`", which costs a submission to discover.
theorem solution {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℝ)
    (hdeg : ∀ i, (p i).totalDegree ≤ 2) :
    ∃ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ 4 ∧
      ∀ x : Fin n → ℝ,
        (MvPolynomial.eval x f = 0 ↔ ∀ i, MvPolynomial.eval x (p i) = 0) := by
  refine ⟨∑ i, p i ^ 2, ?_, ?_⟩
  · -- The total degree of a sum is at most the largest total degree of a
    -- summand, and squaring at most doubles it.
    refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun i _ => ?_)
    calc (p i ^ 2).totalDegree
        ≤ 2 * (p i).totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ 2 * 2 := by gcongr; exact hdeg i
      _ = 4 := by norm_num
  · -- Evaluation is a ring hom, so the value at `x` is a finite sum of real
    -- squares. Such a sum vanishes exactly when every square vanishes.
    intro x
    rw [map_sum]
    simp only [map_pow]
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (eval x (p i))]
    simp

/-- First companion at a concrete family, to witness that the conclusion is not -/
example : ∃ f : MvPolynomial (Fin 1) ℝ, f.totalDegree ≤ 4 ∧
    ∀ x : Fin 1 → ℝ, MvPolynomial.eval x f ≠ 0 := by
  obtain ⟨f, hdeg, hzero⟩ :=
    solution (n := 1) (m := 2) ![X 0, C 1] (by intro i; fin_cases i <;> simp)
  refine ⟨f, hdeg, fun x hx => ?_⟩
  have h := (hzero x).mp hx 1
  simp at h

/-- Second companion at a concrete family, to witness that the conclusion is not -/
example : ∃ f : MvPolynomial (Fin 1) ℝ, f.totalDegree ≤ 4 ∧
    MvPolynomial.eval ![(0 : ℝ)] f = 0 ∧ MvPolynomial.eval ![(1 : ℝ)] f ≠ 0 := by
  obtain ⟨f, hdeg, hzero⟩ :=
    solution (n := 1) (m := 1) ![X 0] (by intro i; fin_cases i; simp)
  refine ⟨f, hdeg, (hzero _).mpr (by intro i; fin_cases i; simp), fun hx => ?_⟩
  have h := (hzero _).mp hx 0
  simp at h

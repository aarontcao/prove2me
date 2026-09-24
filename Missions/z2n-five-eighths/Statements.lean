import Missions.«z2n-five-eighths».Definitions

/-!
Draft mission items for the five-eighths conjecture in `ZMod (2^n)`, each
ending in `:= by sorry`. The goal (Long-Wagner Conjecture 5.1) is open.
-/

namespace Z2nFiveEighths

/-- **The goal.** Long-Wagner Conjecture 5.1, open since 2018. -/
theorem cubeFree_card_le_five_eighths (n : ℕ) (hn : 4 ≤ n)
    (A : Finset (ZMod (2 ^ n))) (hA : CubeFree A) :
    8 * A.card ≤ 5 * 2 ^ n := by sorry

/-- **Milestone `upperBoundLayers`.** Long-Wagner Theorem 1.10 at `d = 3`: the -/
theorem cubeFree_layerUnion_card_le_five_eighths (n : ℕ) (hn : 4 ≤ n)
    (A : Finset (ZMod (2 ^ n))) (hlayer : IsLayerUnion n A) (hA : CubeFree A) :
    8 * A.card ≤ 5 * 2 ^ n := by sorry

/-- **Milestone `cubeFree_two_thirds`.** The best unconditional constant this -/
theorem cubeFree_card_le_two_thirds (n : ℕ) (A : Finset (ZMod (2 ^ n)))
    (hA : CubeFree A) : 3 * A.card + 1 ≤ 2 ^ (n + 1) := by sorry

/-- **Milestone `upperBound_four`.** The conjecture at `n = 4`. -/
theorem cubeFree_card_le_five_eighths_four (A : Finset (ZMod (2 ^ 4)))
    (hA : CubeFree A) : 8 * A.card ≤ 5 * 2 ^ 4 := by sorry

/-- **Milestone `upperBound_five`.** The conjecture at `n = 5`. -/
theorem cubeFree_card_le_five_eighths_five (A : Finset (ZMod (2 ^ 5)))
    (hA : CubeFree A) : 8 * A.card ≤ 5 * 2 ^ 5 := by sorry

/-- **Milestone `baseCase8`.** The base case, by exhaustion over all 256 subsets -/
theorem cubeFree_mod_eight_card_le_five (A : Finset (ZMod 8)) (hA : CubeFree A) :
    A.card ≤ 5 := by sorry

/-- **Milestone `oddsCase`.** The tight case of the induction. -/
theorem cubeFree_containing_odds (N : ℕ) [NeZero N] (hN : (8 : ℕ) ∣ N)
    (A : Finset (ZMod N)) (hA : CubeFree A)
    (hodd : ∀ x : ZMod N, x.val % 2 = 1 → x ∈ A) :
    8 * A.card ≤ 5 * N := by sorry

/-- **Milestone `sharp`.** The constant 5/8 is not improvable. -/
theorem five_eighths_attained (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Finset (ZMod (2 ^ n)), CubeFree A ∧ 8 * A.card = 5 * 2 ^ n := by sorry

/-- **Milestone `bridge`.** The two encodings of the forbidden configuration -/
theorem cubeFree_iff_configFree {G : Type} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) : CubeFree A ↔ ConfigFree A := by sorry

/-- **Milestone `monotone`.** Cube-freeness passes to subsets. -/
theorem cubeFree_subset {G : Type} [AddCommGroup G] (A B : Finset G)
    (hBA : B ⊆ A) (hA : CubeFree A) : CubeFree B := by sorry

end Z2nFiveEighths

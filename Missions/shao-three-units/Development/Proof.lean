import Missions.«shao-three-units».Development.Statements

/-!
Shao's argument through Corollary 1.5, 140 declarations free of `sorry`,
`native_decide`, and any axiom outside `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace ShaoThreeUnits.Proof

open Finset
open scoped Pointwise

/-- The unit classes mod `m` number `phi m`. The `Finset` of units is the image
of the unit group under `Units.val`, that map is injective, and Mathlib already
counts the unit group as `Nat.totient m`, so the three facts compose. -/
theorem card_U : Statements.CardU := by
  intro m _
  classical
  have h : Statements.U m = Finset.univ.image (Units.val : (ZMod m)ˣ → ZMod m) := by
    ext x
    constructor
    · intro hx
      have hu : IsUnit x := by simpa [Statements.U] using hx
      obtain ⟨u, hu⟩ := hu
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, hu⟩
    · intro hx
      obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hx
      have : IsUnit x := hu ▸ u.isUnit
      simpa [Statements.U] using this
  rw [h, Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ,
    ZMod.card_units_eq_totient]

/-- Cauchy-Davenport-Chowla for three sets mod a prime. Two applications of
Mathlib's two-set `ZMod.cauchy_davenport` push the sumset up to size `p`, and a
subset of `ZMod p` with `p` elements is everything. -/
theorem cd_chowla : Statements.CDChowla := by
  intro p hp I J K hI hJ hK hsize x
  classical
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hI1 : 1 ≤ I.card := Finset.card_pos.mpr hI
  have hJ1 : 1 ≤ J.card := Finset.card_pos.mpr hJ
  have hK1 : 1 ≤ K.card := Finset.card_pos.mpr hK
  have hIJ : (I + J).Nonempty := hI.add hJ
  have h1 : min p (I.card + J.card - 1) ≤ (I + J).card :=
    ZMod.cauchy_davenport hp hI hJ
  have h2 : min p ((I + J).card + K.card - 1) ≤ (I + J + K).card :=
    ZMod.cauchy_davenport hp hIJ hK
  have hcard : p ≤ (I + J + K).card := by omega
  have huniv : I + J + K = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hle : (I + J + K).card ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
    rw [ZMod.card p] at hle ⊢
    omega
  have hx : x ∈ I + J + K := huniv ▸ Finset.mem_univ x
  rw [Finset.mem_add] at hx
  obtain ⟨y, hy, w, hw, rfl⟩ := hx
  rw [Finset.mem_add] at hy
  obtain ⟨u, hu, v, hv, rfl⟩ := hy
  exact ⟨u, hu, v, hv, w, hw, rfl⟩

/-! ## Anti-vacuity

Each proved node, instantiated at a concrete value. A statement quantified over
an empty class cannot produce one of these, so these witnesses are the check
that an inspection of the axiom closure cannot make.
-/

/-- `card_U` at `m = 15`, where the units really are 8 classes rather than 0. -/
example : (Statements.U 15).card = 8 := by rw [card_U]; decide

/-- `cd_chowla` at `p = 5` with `I = J = K = {1,2,3}`. The size hypothesis
`5 + 2 ≤ 3 + 3 + 3` holds, so the theorem applies and returns an actual
representation of `0` as a sum of three elements, which is more than a
consistency check, because it shows the hypotheses can be met. -/
example : ∃ u ∈ ({1, 2, 3} : Finset (ZMod 5)), ∃ v ∈ ({1, 2, 3} : Finset (ZMod 5)),
    ∃ w ∈ ({1, 2, 3} : Finset (ZMod 5)), u + v + w = (0 : ZMod 5) :=
  cd_chowla 5 (by norm_num) _ _ _ ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩
    (by decide) 0


/-! ## Node `lemma_2_3`: the finite check at `m = 15`, by Chinese Remainder

The paper discharges this step with a computer check over about `2 * 10^5` set
triples. A kernel `decide` will not finish that check, and `native_decide` is
not permitted here, so the development takes a different route and removes the
enumeration altogether.

The key observation is that `ZMod 15` splits as `ZMod 3 × ZMod 5`, so writing
each of `A`, `B`, and `C` as its two fibers over the units mod 3 turns
`A + B + C = ZMod 15` into three covering conditions in `ZMod 5`, one for each
residue mod 3 and each with its sign pattern fixed. Cauchy-Davenport in `ZMod 5`
covers on its own whenever a pattern has three nonempty fibers whose sizes add
to at least 7, and `shao_lemma23_arith` shows by kernel `decide` that Shao's
hypothesis always supplies such a pattern; all 2205 admissible fiber-size tuples
are settled there, and no case is left over.
-/

-- The kernel `decide` in `shao_lemma23_arith` needs this recursion depth and
-- nothing after `end` does, so the option is scoped; left unscoped it would
-- also cover `lemma_2_1`.
section DeepRecursion
set_option maxRecDepth 100000

/-! ## The CRT coordinates on `ZMod 15`

`ZMod 15 ≃ ZMod 3 × ZMod 5`, and a unit mod 15 is a unit in each coordinate.
Only the injectivity half of the equivalence is needed anywhere below, and at
this size that half is a kernel `decide` over 225 pairs. -/

/-- Reduction `ZMod 15 →+* ZMod 3`. -/
def q3 : ZMod 15 →+* ZMod 3 := ZMod.castHom (by norm_num) (ZMod 3)

/-- Reduction `ZMod 15 →+* ZMod 5`. -/
def q5 : ZMod 15 →+* ZMod 5 := ZMod.castHom (by norm_num) (ZMod 5)

/-- The CRT map `ZMod 15 → ZMod 3 × ZMod 5` is injective. Injectivity alone is
all the argument draws from the Chinese remainder equivalence, and it suffices
to turn a single identity in `ZMod 15` into the pair of identities mod 3 and
mod 5. -/
theorem crt_inj : ∀ y z : ZMod 15, q3 y = q3 z → q5 y = q5 z → y = z := by decide

/-- `ZMod 3` has exactly the three elements `0`, `1`, `2`. -/
theorem zmod3_cases : ∀ y : ZMod 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide

/-- The units mod 15, listed. `Statements.U` is a `Classical` filter on
`IsUnit`, so it is not itself decidable, and `isUnit_iff_exists_inv` replaces it
by an existential over a `Fintype`, which is. -/
theorem U15 : Statements.U 15 = ({1, 2, 4, 7, 8, 11, 13, 14} : Finset (ZMod 15)) := by
  ext x
  simp only [Statements.U, Finset.mem_filter, Finset.mem_univ, true_and,
    isUnit_iff_exists_inv]
  revert x
  decide

/-- A unit mod 15 reduces to a unit mod 3, that is to `1` or `2`. -/
theorem q3_unit : ∀ a : ZMod 15, a ∈ ({1, 2, 4, 7, 8, 11, 13, 14} : Finset (ZMod 15)) →
    q3 a = 1 ∨ q3 a = 2 := by decide

/-- A unit mod 15 reduces to a unit mod 5, that is to `1`, `2`, `3`, or `4`. -/
theorem q5_unit : ∀ a : ZMod 15, a ∈ ({1, 2, 4, 7, 8, 11, 13, 14} : Finset (ZMod 15)) →
    q5 a ∈ ({1, 2, 3, 4} : Finset (ZMod 5)) := by decide

/-! ## Fibers

`A` is cut into its two fibers over the units mod 3, each of them recorded as a
subset of `ZMod 5`. Injectivity of the CRT map makes each fiber the same size as
its preimage, so the two fiber sizes add to `|A|`. -/

/-- The fiber of `A` over `i : ZMod 3`, pushed into `ZMod 5`. -/
def fib (A : Finset (ZMod 15)) (i : ZMod 3) : Finset (ZMod 5) :=
  (A.filter (fun a => q3 a = i)).image q5

theorem mem_fib {A : Finset (ZMod 15)} {i : ZMod 3} {u : ZMod 5} :
    u ∈ fib A i ↔ ∃ a ∈ A, q3 a = i ∧ q5 a = u := by
  constructor
  · intro h
    obtain ⟨a, ha, hu⟩ := Finset.mem_image.mp h
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    exact ⟨a, ha1, ha2, hu⟩
  · rintro ⟨a, ha, h3, h5⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, h3⟩, h5⟩

/-- Pushing a fiber into `ZMod 5` loses nothing, because two elements of `A`
with the same image mod 3 and the same image mod 5 are equal. -/
theorem card_fib (A : Finset (ZMod 15)) (i : ZMod 3) :
    (fib A i).card = (A.filter (fun a => q3 a = i)).card := by
  apply Finset.card_image_of_injOn
  intro y hy z hz h
  exact crt_inj y z (by rw [(Finset.mem_filter.mp hy).2, (Finset.mem_filter.mp hz).2]) h

/-- The two fiber sizes add to `|A|`, because every unit mod 15 lands in one of
the two unit classes mod 3. -/
theorem card_split {A : Finset (ZMod 15)} (hA : A ⊆ Statements.U 15) :
    (fib A 1).card + (fib A 2).card = A.card := by
  rw [card_fib, card_fib]
  have hsw : A.filter (fun a => q3 a = 2) = A.filter (fun a => ¬ (q3 a = 1)) := by
    apply Finset.filter_congr
    intro a ha
    rcases q3_unit a (U15 ▸ hA ha) with h | h <;> rw [h] <;> decide
  rw [hsw]
  exact Finset.card_filter_add_card_filter_not (fun a => q3 a = 1)

/-- A fiber sits inside the four units of `ZMod 5`, so it has at most 4 elements. -/
theorem card_fib_lt {A : Finset (ZMod 15)} (hA : A ⊆ Statements.U 15) (i : ZMod 3) :
    (fib A i).card < 5 := by
  have hsub : fib A i ⊆ ({1, 2, 3, 4} : Finset (ZMod 5)) := by
    intro u hu
    obtain ⟨a, ha, -, rfl⟩ := mem_fib.mp hu
    exact q5_unit a (U15 ▸ hA ha)
  have hle := Finset.card_le_card hsub
  have h4 : ({1, 2, 3, 4} : Finset (ZMod 5)).card = 4 := by decide
  omega

/-! ## One covering step

Fix a sign pattern `(i, j, k)` of unit classes mod 3 whose sum matches `x` mod 3.
If the three fibers over that pattern are nonempty and their sizes add to at
least `7 = 5 + 2`, then `cd_chowla` at `p = 5` covers `ZMod 5`, and injectivity
of the CRT map lifts the representation it produces back to `ZMod 15`. -/

theorem step {A B C : Finset (ZMod 15)} {i j k : ZMod 3} {x : ZMod 15}
    (hijk : i + j + k = q3 x)
    (h1 : 0 < (fib A i).card) (h2 : 0 < (fib B j).card) (h3 : 0 < (fib C k).card)
    (hsz : 7 ≤ (fib A i).card + (fib B j).card + (fib C k).card) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + b + c = x := by
  obtain ⟨u, hu, v, hv, w, hw, huvw⟩ :=
    cd_chowla 5 (by norm_num) (fib A i) (fib B j) (fib C k)
      (Finset.card_pos.mp h1) (Finset.card_pos.mp h2) (Finset.card_pos.mp h3)
      (by omega) (q5 x)
  obtain ⟨a, ha, ha3, ha5⟩ := mem_fib.mp hu
  obtain ⟨b, hb, hb3, hb5⟩ := mem_fib.mp hv
  obtain ⟨c, hc, hc3, hc5⟩ := mem_fib.mp hw
  refine ⟨a, ha, b, hb, c, hc, ?_⟩
  refine crt_inj _ _ ?_ ?_
  · rw [map_add, map_add, ha3, hb3, hc3, hijk]
  · rw [map_add, map_add, ha5, hb5, hc5, huvw]

/-! ## The arithmetic core

Shao's size hypothesis, read in fiber sizes, always supplies a usable pattern for
each of the three residues mod 3 at once. The kernel checks all `5 ^ 6`
fiber-size tuples, and every one of the 2205 that satisfy the hypothesis yields
a pattern. -/

/-- The arithmetic core of the CRT reduction for Shao's Lemma 2.3. -/
theorem shao_lemma23_arith :
    ∀ a0 a1 b0 b1 c0 c1 : Fin 5,
      5 * ((a0.val + a1.val) + (b0.val + b1.val) + (c0.val + c1.val))
          < (a0.val + a1.val) * (b0.val + b1.val)
            + (b0.val + b1.val) * (c0.val + c1.val)
            + (c0.val + c1.val) * (a0.val + a1.val) →
      ((0 < a0.val ∧ 0 < b0.val ∧ 0 < c0.val ∧ 7 ≤ a0.val + b0.val + c0.val) ∨
       (0 < a1.val ∧ 0 < b1.val ∧ 0 < c1.val ∧ 7 ≤ a1.val + b1.val + c1.val)) ∧
      ((0 < a1.val ∧ 0 < b0.val ∧ 0 < c0.val ∧ 7 ≤ a1.val + b0.val + c0.val) ∨
       (0 < a0.val ∧ 0 < b1.val ∧ 0 < c0.val ∧ 7 ≤ a0.val + b1.val + c0.val) ∨
       (0 < a0.val ∧ 0 < b0.val ∧ 0 < c1.val ∧ 7 ≤ a0.val + b0.val + c1.val)) ∧
      ((0 < a0.val ∧ 0 < b1.val ∧ 0 < c1.val ∧ 7 ≤ a0.val + b1.val + c1.val) ∨
       (0 < a1.val ∧ 0 < b0.val ∧ 0 < c1.val ∧ 7 ≤ a1.val + b0.val + c1.val) ∨
       (0 < a1.val ∧ 0 < b1.val ∧ 0 < c0.val ∧ 7 ≤ a1.val + b1.val + c0.val)) := by
  decide

/-- `shao_lemma23_arith` with the `Fin 5` bounds stated as hypotheses, which is
the shape the fiber sizes arrive in. -/
theorem shao_arith_nat (a0 a1 b0 b1 c0 c1 : ℕ)
    (ha0 : a0 < 5) (ha1 : a1 < 5) (hb0 : b0 < 5) (hb1 : b1 < 5)
    (hc0 : c0 < 5) (hc1 : c1 < 5)
    (h : 5 * ((a0 + a1) + (b0 + b1) + (c0 + c1))
          < (a0 + a1) * (b0 + b1) + (b0 + b1) * (c0 + c1) + (c0 + c1) * (a0 + a1)) :
      ((0 < a0 ∧ 0 < b0 ∧ 0 < c0 ∧ 7 ≤ a0 + b0 + c0) ∨
       (0 < a1 ∧ 0 < b1 ∧ 0 < c1 ∧ 7 ≤ a1 + b1 + c1)) ∧
      ((0 < a1 ∧ 0 < b0 ∧ 0 < c0 ∧ 7 ≤ a1 + b0 + c0) ∨
       (0 < a0 ∧ 0 < b1 ∧ 0 < c0 ∧ 7 ≤ a0 + b1 + c0) ∨
       (0 < a0 ∧ 0 < b0 ∧ 0 < c1 ∧ 7 ≤ a0 + b0 + c1)) ∧
      ((0 < a0 ∧ 0 < b1 ∧ 0 < c1 ∧ 7 ≤ a0 + b1 + c1) ∨
       (0 < a1 ∧ 0 < b0 ∧ 0 < c1 ∧ 7 ≤ a1 + b0 + c1) ∨
       (0 < a1 ∧ 0 < b1 ∧ 0 < c0 ∧ 7 ≤ a1 + b1 + c0)) :=
  shao_lemma23_arith ⟨a0, ha0⟩ ⟨a1, ha1⟩ ⟨b0, hb0⟩ ⟨b1, hb1⟩ ⟨c0, hc0⟩ ⟨c1, hc1⟩ h

/-! ## Assembly -/

/-- Shao's Lemma 2.3, the finite check at `m = 15`, with the finite check
replaced by a Chinese Remainder reduction. `ZMod 15` splits as
`ZMod 3 × ZMod 5`, the size hypothesis hands each residue mod 3 a sign pattern
whose three fibers are nonempty with sizes adding to at least `7`, and
Cauchy-Davenport-Chowla in `ZMod 5` covers from there. No enumeration of set
triples appears anywhere in the proof. -/
theorem lemma_2_3 : Statements.Lemma23 := by
  intro A B C hA hB hC hsize x
  obtain ⟨H0, H1, H2⟩ :=
    shao_arith_nat (fib A 1).card (fib A 2).card (fib B 1).card (fib B 2).card
      (fib C 1).card (fib C 2).card
      (card_fib_lt hA 1) (card_fib_lt hA 2) (card_fib_lt hB 1) (card_fib_lt hB 2)
      (card_fib_lt hC 1) (card_fib_lt hC 2)
      (by rw [card_split hA, card_split hB, card_split hC]; exact hsize)
  rcases zmod3_cases (q3 x) with h | h | h
  · -- `x ≡ 0 mod 3`: the patterns are `(1,1,1)` and `(2,2,2)`
    rcases H0 with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩
    · exact step (i := 1) (j := 1) (k := 1) (by rw [h]; decide) p1 p2 p3 p4
    · exact step (i := 2) (j := 2) (k := 2) (by rw [h]; decide) p1 p2 p3 p4
  · -- `x ≡ 1 mod 3`: the patterns are the permutations of `(1,1,2)`
    rcases H1 with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩
    · exact step (i := 2) (j := 1) (k := 1) (by rw [h]; decide) p1 p2 p3 p4
    · exact step (i := 1) (j := 2) (k := 1) (by rw [h]; decide) p1 p2 p3 p4
    · exact step (i := 1) (j := 1) (k := 2) (by rw [h]; decide) p1 p2 p3 p4
  · -- `x ≡ 2 mod 3`: the patterns are the permutations of `(1,2,2)`
    rcases H2 with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩
    · exact step (i := 1) (j := 2) (k := 2) (by rw [h]; decide) p1 p2 p3 p4
    · exact step (i := 2) (j := 1) (k := 2) (by rw [h]; decide) p1 p2 p3 p4
    · exact step (i := 2) (j := 2) (k := 1) (by rw [h]; decide) p1 p2 p3 p4

/-! ## Anti-vacuity -/

/-- `lemma_2_3` at `A = B = C = U 15`. The unit group has 8 elements, so
`5 * (8 + 8 + 8) = 120 < 192 = 8 * 8 + 8 * 8 + 8 * 8` and the hypothesis is met,
after which the theorem returns an actual representation of `0`, which a
statement quantified over an empty class could not produce. -/
example : ∃ a ∈ Statements.U 15, ∃ b ∈ Statements.U 15, ∃ c ∈ Statements.U 15,
    a + b + c = (0 : ZMod 15) := by
  have hcard : (Statements.U 15).card = 8 := by rw [card_U]; decide
  exact lemma_2_3 _ _ _ (subset_refl _) (subset_refl _) (subset_refl _)
    (by rw [hcard]; norm_num) 0

/-- The extremal sizes really are excluded, since at `|A| = |B| = |C| = 5` the
hypothesis reads `75 < 75` and so fails. That is Shao's sharp example, and the
inequality is strict in order to exclude it. -/
example : ¬ (5 * (5 + 5 + 5) < 5 * 5 + 5 * 5 + 5 * 5) := by norm_num

/-! ## The index map `nu`, shared by both averaging lemmas

For `i, j < m` there is exactly one `k` in `[m, 2m)` with `m ∣ i + j + k`, and
that `k` is `m + nu m i j`. Writing `nu` by cases on `i + j`, instead of through
`%`, is what makes every side condition below fall to `omega`.

For fixed `i` the map `j ↦ nu m i j` is an involution of `range m`, so `nu_row`
says a row sum reindexes to the plain tail sum. `lemma_2_1` uses this machinery
once over one index square and `lemma_2_2` uses it four times over four
different squares, so it lives at top level rather than inside either proof.
-/

private def nu (m i j : ℕ) : ℕ :=
  if i + j = 0 then 0 else if i + j ≤ m then m - (i + j) else 2 * m - (i + j)

private theorem nu_lt (m i j : ℕ) (hi : i < m) (hj : j < m) : nu m i j < m := by
  simp only [nu]
  split_ifs <;> omega

private theorem nu_symm (m i j : ℕ) : nu m i j = nu m j i := by
  simp only [nu, Nat.add_comm i j]

private theorem nu_zero (m : ℕ) : nu m 0 0 = 0 := by simp [nu]

private theorem nu_adm (m i j : ℕ) (hi : i < m) (hj : j < m) (hne : ¬ (i = 0 ∧ j = 0)) :
    2 * m ≤ i + j + (m + nu m i j) := by
  -- the third branch subtracts `i + j` from `2 * m`, so it needs `i + j < 2 * m`
  have h2 : i + j < m + m := Nat.add_lt_add hi hj
  simp only [nu]
  split_ifs <;> omega

private theorem nu_invol (m i j : ℕ) (hi : i < m) (hj : j < m) :
    nu m i (nu m i j) = j := by
  have h1 : nu m i j < m := nu_lt m i j hi hj
  simp only [nu] at h1 ⊢
  split_ifs at h1 ⊢ <;> omega

/-- The row sum. For fixed `i < m`, summing any `h` along `j ↦ m + nu m i j` over
`range m` is the same as summing `h` over the whole tail block `[m, 2m)`, because
`j ↦ nu m i j` is an involution of `range m`. Generic in `h`, since the two
averaging lemmas need it at three different sequences. -/
private theorem nu_row (m : ℕ) (h : ℕ → ℝ) (i : ℕ) (hi : i < m) :
    ∑ j ∈ range m, h (m + nu m i j) = ∑ s ∈ range m, h (m + s) := by
  have hinj : ∀ p ∈ range m, ∀ q ∈ range m, nu m i p = nu m i q → p = q := by
    intro p hp q hq hpq
    rw [Finset.mem_range] at hp hq
    have hpp := nu_invol m i p hi hp
    rw [hpq, nu_invol m i q hi hq] at hpp
    omega
  have himg : (range m).image (nu m i) = range m := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro s hs
      simp only [Finset.mem_image, Finset.mem_range] at hs ⊢
      obtain ⟨j, hj, rfl⟩ := hs
      exact nu_lt m i j hi hj
    · rw [Finset.card_image_of_injOn (fun p hp q hq hpq => hinj p hp q hq hpq)]
  have key : ∑ s ∈ (range m).image (nu m i), h (m + s)
      = ∑ j ∈ range m, h (m + nu m i j) :=
    Finset.sum_image (fun p hp q hq hpq => hinj p hp q hq hpq)
  rw [← key, himg]

/-! ## Node `lemma_2_1`: the symmetric averaging inequality

Shao's Lemma 2.1, formalized from the proof in arXiv:1206.6139v2, pages 4 to 5.

The argument runs as follows. Substitute `x i = 16/5 * a i - 1`, which turns
the hypothesis into `x i * x j + x j * x k + x k * x i <= 3` and the goal
into `sum x i <= n`, and suppose that goal fails. Write `n = 2m` and split the
sum into `S0` over the first `m` indices and `S1` over the last `m`, then sum
the hypothesis over the `m^2` triples `(i, j, k)` with `i, j < m <= k < 2m` and
`i + j + k = 0 mod m`. That sum equals `S0^2 + 2*S0*S1`, and every triple in it
except `(0, 0, m)` is admissible, so the corner has to be added back by hand;
what is left after that is a split on the sign of `S1`.

Three points in the sketch above are easy to lose, and a first attempt at the
formalization lost all three of them.

The reindexing runs through three separate bijections, one for each term of the
summand, and each of the three needs its own argument, so a single telescoping
substitution does not deliver it. The third index here is `m + nu i j`, where
`nu i j` depends only on `i + j` and is written by cases instead of through `%`,
so that every side condition falls to `omega`. For fixed `i` the map
`j |-> nu i j` is an involution of `range m`, and `hrow` turns that involution
into `sum_j x (m + nu i j) = S1`.

The corner triple `(0, 0, m)` lies outside the range the hypothesis covers, so
its value `x 0 ^ 2 + 2 * x 0 * x m` has to be added back, and bounding it calls
on the hypothesis at the triple `(m, m, 0)`, which is not one of the `m^2`
triples either.

The case `S1 > 0` calls on the hypothesis at `(m, m, m)` as well, which gives
`x m ^ 2 <= 1`. So the hypothesis is used at three kinds of triple, and two of
the three sit outside the summation.

`6 <= n` enters at exactly two numeric thresholds, both of which need `m >= 3`,
namely `24 * m^2 > 121` in the first case and
`(m^2 - 7) * (25 * m^2 - 21) > 0` in the second. The paper's counterexample at `n = 4` is recorded below as a witness.

The hypothesis `0 <= a i` is never used in this proof, and it is kept in the
statement anyway, because that statement is the one the paper publishes.
-/

set_option maxHeartbeats 1000000 in
-- The reindexing identity `hprod` elaborates three nested `Finset` sums over the
-- `m × m` square, and the endgame runs several `nlinarith` calls in the variable `v`.
theorem lemma_2_1 : Statements.Lemma21 := by
  intro n hn6 hev a hanti ha0 ha1 hyp
  by_contra hgoal
  replace hgoal : (5 : ℝ) / 8 * n < ∑ i, a i := not_le.mp hgoal
  obtain ⟨m, hm⟩ := hev
  have hm3 : 3 ≤ m := by omega
  have hn0 : 0 < n := by omega
  -- the shifted variables, extended to all of ℕ by clamping the index
  set f : ℕ → Fin n := fun i => ⟨min i (n - 1), by omega⟩ with hfdef
  set x : ℕ → ℝ := fun i => 16 / 5 * a (f i) - 1 with hxdef
  have hfval : ∀ i (h : i < n), f i = ⟨i, h⟩ := by
    intro i h
    apply Fin.val_injective
    simp only [hfdef]
    omega
  have hxlt : ∀ i (h : i < n), x i = 16 / 5 * a ⟨i, h⟩ - 1 := by
    intro i h
    rw [hxdef]
    simp only
    rw [hfval i h]
  have hxanti : ∀ i j : ℕ, i ≤ j → x j ≤ x i := by
    intro i j hij
    have hle : f i ≤ f j := by
      simp only [hfdef, Fin.mk_le_mk]
      omega
    have := hanti hle
    simp only [hxdef]
    linarith
  have hxub : ∀ i : ℕ, x i ≤ 11 / 5 := by
    intro i
    have := ha1 (f i)
    simp only [hxdef]
    linarith
  -- the hypothesis in the shifted variables
  have hx3 : ∀ i j k : ℕ, i < n → j < n → k < n → n ≤ i + j + k →
      x i * x j + x j * x k + x k * x i ≤ 3 := by
    intro i j k hi hj hk hsum
    have h := hyp ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ (by simpa using hsum)
    rw [hxlt i hi, hxlt j hj, hxlt k hk]
    nlinarith [h]
  -- the sum grows past n
  have hsumtrans : ∑ i ∈ range n, x i = 16 / 5 * (∑ i, a i) - n := by
    have h1 : ∑ i : Fin n, x (i : ℕ) = ∑ i ∈ range n, x i :=
      Fin.sum_univ_eq_sum_range (fun i => x i) n
    rw [← h1]
    have h2 : ∀ i : Fin n, x (i : ℕ) = 16 / 5 * a i - 1 := by
      intro i
      rw [hxlt (i : ℕ) i.isLt]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
  have hbig : (n : ℝ) < ∑ i ∈ range n, x i := by
    rw [hsumtrans]; linarith
  -- the two halves
  set S0 : ℝ := ∑ i ∈ range m, x i with hS0def
  set S1 : ℝ := ∑ s ∈ range m, x (m + s) with hS1def
  have hsplit : S0 + S1 = ∑ i ∈ range n, x i := by
    rw [hS0def, hS1def, hm]
    exact (Finset.sum_range_add (fun i => x i) m m).symm
  have hnR : ((n : ℕ) : ℝ) = 2 * (m : ℝ) := by rw [hm]; push_cast; ring
  have hT : 2 * (m : ℝ) < S0 + S1 := by
    rw [hsplit, ← hnR]; exact hbig
  have hS0ub : S0 ≤ 11 / 5 * m := by
    rw [hS0def]
    calc ∑ i ∈ range m, x i ≤ ∑ _i ∈ range m, (11 / 5 : ℝ) :=
          Finset.sum_le_sum (fun i _ => hxub i)
      _ = 11 / 5 * m := by simp [mul_comm]
  have hS1lo : -((m : ℝ) / 5) < S1 := by linarith
  have hx0 : 1 < x 0 := by
    by_contra hc
    replace hc : x 0 ≤ 1 := not_lt.mp hc
    have hall : ∀ i ∈ range n, x i ≤ 1 := fun i _ => le_trans (hxanti 0 i (Nat.zero_le i)) hc
    have hle : ∑ i ∈ range n, x i ≤ ∑ _i ∈ range n, (1 : ℝ) := Finset.sum_le_sum hall
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hle
    linarith
  have hx0ub : x 0 ≤ 11 / 5 := hxub 0
  -- the row sum, from the top-level `nu` machinery
  have hrow : ∀ i : ℕ, i < m → ∑ j ∈ range m, x (m + nu m i j) = S1 := by
    intro i hi
    rw [hS1def]
    exact nu_row m x i hi
  -- the reindexing identity
  have hprod : ∑ p ∈ range m ×ˢ range m,
      (x p.1 * x p.2 + x p.2 * x (m + nu m p.1 p.2) + x (m + nu m p.1 p.2) * x p.1)
      = S0 ^ 2 + 2 * S0 * S1 := by
    rw [Finset.sum_product]
    have e1 : ∑ i ∈ range m, ∑ j ∈ range m, x i * x j = S0 ^ 2 := by
      rw [hS0def, sq, Finset.sum_mul_sum]
    have e2 : ∑ i ∈ range m, ∑ j ∈ range m, x j * x (m + nu m i j) = S0 * S1 := by
      rw [Finset.sum_comm, hS0def, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [← Finset.mul_sum]
      congr 1
      have hs : ∀ i ∈ range m, x (m + nu m i j) = x (m + nu m j i) := by
        intro i _; rw [nu_symm m i j]
      rw [Finset.sum_congr rfl hs, hrow j hj]
    have e3 : ∑ i ∈ range m, ∑ j ∈ range m, x (m + nu m i j) * x i = S0 * S1 := by
      rw [hS0def, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [← Finset.sum_mul, hrow i hi]
      exact mul_comm S1 (x i)
    calc ∑ i ∈ range m, ∑ j ∈ range m,
            (x i * x j + x j * x (m + nu m i j) + x (m + nu m i j) * x i)
        = (∑ i ∈ range m, ∑ j ∈ range m, x i * x j)
          + (∑ i ∈ range m, ∑ j ∈ range m, x j * x (m + nu m i j))
          + (∑ i ∈ range m, ∑ j ∈ range m, x (m + nu m i j) * x i) := by
          simp only [Finset.sum_add_distrib]
      _ = S0 ^ 2 + 2 * S0 * S1 := by rw [e1, e2, e3]; ring
  -- sum the hypothesis over the punctured square
  have hmem00 : ((0 : ℕ), (0 : ℕ)) ∈ range m ×ˢ range m := by
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  have herase : ∑ p ∈ (range m ×ˢ range m).erase (0, 0),
      (x p.1 * x p.2 + x p.2 * x (m + nu m p.1 p.2) + x (m + nu m p.1 p.2) * x p.1)
      ≤ 3 * ((m : ℝ) ^ 2 - 1) := by
    have hbound : ∀ p ∈ (range m ×ˢ range m).erase (0, 0),
        x p.1 * x p.2 + x p.2 * x (m + nu m p.1 p.2)
          + x (m + nu m p.1 p.2) * x p.1 ≤ 3 := by
      rintro ⟨i, j⟩ hp
      rw [Finset.mem_erase, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      obtain ⟨hne, hi, hj⟩ := hp
      have hne' : ¬ (i = 0 ∧ j = 0) := by
        rintro ⟨rfl, rfl⟩; exact hne rfl
      have hkl : m + nu m i j < n := by
        have := nu_lt m i j hi hj; omega
      exact hx3 i j (m + nu m i j) (by omega) (by omega) hkl (by
        have := nu_adm m i j hi hj hne'; omega)
    have hcard : ((range m ×ˢ range m).erase (0, 0)).card = m * m - 1 := by
      rw [Finset.card_erase_of_mem hmem00, Finset.card_product, Finset.card_range]
    calc ∑ p ∈ (range m ×ˢ range m).erase (0, 0),
            (x p.1 * x p.2 + x p.2 * x (m + nu m p.1 p.2)
              + x (m + nu m p.1 p.2) * x p.1)
        ≤ ∑ _p ∈ (range m ×ˢ range m).erase (0, 0), (3 : ℝ) :=
          Finset.sum_le_sum hbound
      _ = ((m * m - 1 : ℕ) : ℝ) * 3 := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ = 3 * ((m : ℝ) ^ 2 - 1) := by
          have h1 : 1 ≤ m * m := by nlinarith
          rw [Nat.cast_sub h1]
          push_cast
          ring
  -- the corner term
  have hcorner : ∑ p ∈ (range m ×ˢ range m).erase (0, 0),
      (x p.1 * x p.2 + x p.2 * x (m + nu m p.1 p.2) + x (m + nu m p.1 p.2) * x p.1)
      + (x 0 ^ 2 + 2 * (x 0 * x m)) = S0 ^ 2 + 2 * S0 * S1 := by
    rw [← hprod, ← Finset.sum_erase_add (range m ×ˢ range m)
      (fun p : ℕ × ℕ => x p.1 * x p.2 + x p.2 * x (m + nu m p.1 p.2)
        + x (m + nu m p.1 p.2) * x p.1) hmem00]
    congr 1
    simp only [nu_zero]
    ring_nf
  clear_value S0 S1 x f
  -- the two extra uses of the hypothesis
  have hmn : m < n := by omega
  have hmm0 : x m ^ 2 + 2 * (x 0 * x m) ≤ 3 := by
    have h := hx3 m m 0 hmn hmn hn0 (by omega)
    nlinarith [h]
  have hmmm : x m ^ 2 ≤ 1 := by
    have h := hx3 m m m hmn hmn hmn (by omega)
    nlinarith [h]
  -- inequality (4')
  have h4 : S0 ^ 2 + 2 * S0 * S1 ≤ 3 * (m : ℝ) ^ 2 + x 0 ^ 2 - x m ^ 2 := by
    linarith [herase, hcorner, hmm0]
  have h4' : (S0 + S1) ^ 2 ≤ 3 * (m : ℝ) ^ 2 + S1 ^ 2 + x 0 ^ 2 - x m ^ 2 := by
    nlinarith [h4]
  have hm3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have hmsq : (9 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm3R]
  have hTsq : 4 * (m : ℝ) ^ 2 < (S0 + S1) ^ 2 := by
    nlinarith [mul_pos (show (0 : ℝ) < S0 + S1 - 2 * (m : ℝ) by linarith)
      (show (0 : ℝ) < S0 + S1 + 2 * (m : ℝ) by linarith)]
  have hx0sq : x 0 ^ 2 ≤ 121 / 25 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 11 / 5 - x 0 by linarith)
      (show (0 : ℝ) ≤ 11 / 5 + x 0 by linarith)]
  -- case split on the sign of S1
  by_cases hS1 : S1 ≤ 0
  · -- Case 1: the halves nearly cancel
    have hS1sq : S1 ^ 2 ≤ (m : ℝ) ^ 2 / 25 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) / 5 + S1 by linarith)
        (show (0 : ℝ) ≤ (m : ℝ) / 5 - S1 by linarith)]
    linarith [hTsq, h4', hS1sq, hx0sq, hmsq, sq_nonneg (x m)]
  · -- Case 2: the tail is positive, so `x m` is
    replace hS1 : 0 < S1 := not_le.mp hS1
    have hS1le : S1 ≤ (m : ℝ) * x m := by
      rw [hS1def]
      calc ∑ s ∈ range m, x (m + s) ≤ ∑ _s ∈ range m, x m :=
            Finset.sum_le_sum (fun s _ => hxanti m (m + s) (Nat.le_add_right m s))
        _ = (m : ℝ) * x m := by simp [mul_comm]
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hxmpos : 0 < x m := by
      by_contra hc
      replace hc : x m ≤ 0 := not_lt.mp hc
      nlinarith [hS1le, hS1, hmpos]
    obtain ⟨v, hvdef⟩ : ∃ v : ℝ, x m ^ 2 = v := ⟨_, rfl⟩
    rw [hvdef] at h4' hmm0 hmmm
    have hv0 : 0 < v := by rw [← hvdef]; exact pow_pos hxmpos 2
    have hv1 : v ≤ 1 := hmmm
    have hS1sq : S1 ^ 2 ≤ (m : ℝ) ^ 2 * v := by
      have h : S1 * S1 ≤ ((m : ℝ) * x m) * ((m : ℝ) * x m) :=
        mul_self_le_mul_self (le_of_lt hS1) hS1le
      have he : ((m : ℝ) * x m) * ((m : ℝ) * x m) = (m : ℝ) ^ 2 * v := by
        rw [← hvdef]; ring
      linarith [h, he]
    -- inequality (5)
    have h5 : 1 + ((m : ℝ) ^ 2 - 1) * (1 - v) < x 0 ^ 2 := by
      linarith [hTsq, h4', hS1sq]
    -- the corner bound, squared
    have hcbpos : 0 < x 0 * x m := mul_pos (by linarith) hxmpos
    have hcb : x 0 * x m ≤ (3 - v) / 2 := by linarith [hmm0]
    have hsq : x 0 ^ 2 * v ≤ ((3 - v) / 2) ^ 2 := by
      have h : (x 0 * x m) * (x 0 * x m) ≤ ((3 - v) / 2) * ((3 - v) / 2) :=
        mul_self_le_mul_self (le_of_lt hcbpos) hcb
      have he : (x 0 * x m) * (x 0 * x m) = x 0 ^ 2 * v := by rw [← hvdef]; ring
      nlinarith [h, he]
    have hstep : (1 + ((m : ℝ) ^ 2 - 1) * (1 - v)) * v < ((3 - v) / 2) ^ 2 := by
      have h := mul_lt_mul_of_pos_right h5 hv0
      linarith [h, hsq]
    have hA : ((m : ℝ) ^ 2 - 3) * (1 - v) < ((m : ℝ) ^ 2 - 3 / 4) * (1 - v) ^ 2 := by
      linarith [hstep]
    rcases eq_or_lt_of_le hv1 with hveq | hvlt
    · rw [hveq] at hA; linarith [hA]
    · have hu : 0 < 1 - v := by linarith
      have hA' : (m : ℝ) ^ 2 - 3 < ((m : ℝ) ^ 2 - 3 / 4) * (1 - v) := by
        refine lt_of_mul_lt_mul_right ?_ (le_of_lt hu)
        linarith [hA]
      have hB' : ((m : ℝ) ^ 2 - 1) * (1 - v) < 96 / 25 := by
        linarith [h5, hx0sq]
      have hp1 : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by linarith
      have hp2 : (0 : ℝ) < (m : ℝ) ^ 2 - 3 / 4 := by linarith
      have s1 := mul_lt_mul_of_pos_right hA' hp1
      have s2 := mul_lt_mul_of_pos_left hB' hp2
      have s3 : ((m : ℝ) ^ 2 - 3) * ((m : ℝ) ^ 2 - 1)
          < ((m : ℝ) ^ 2 - 3 / 4) * (96 / 25) := by linarith [s1, s2]
      linarith [s3, hmsq, sq_nonneg ((m : ℝ) ^ 2 - 9)]


/-! ### Anti-vacuity for `lemma_2_1`

A witness for this node has to mention the sequence, the hypothesis, and
`Lemma21` itself, since a bare arithmetic fact such as `251/100 > 5/2` would
hold whether or not the node said anything. The two witnesses below apply the
proved theorem to a concrete input, and a third records why `6 ≤ n` cannot be
dropped.
-/

/-- The hypothesis class of `lemma_2_1` is inhabited at `n = 6`, and the bound
is attained there, so the node is neither vacuous nor slack.

The constant sequence `5/8` meets every hypothesis, since the triple condition
reads `3 * (5/8)^2 ≤ 5/8 * (3 * 5/8)` with both sides equal to `75/64`, and its
sum is exactly `5/8 * 6`. The statement below is `lemma_2_1` applied to that
instance, so it also checks that the proved theorem accepts a real input. -/
example : (∑ _i : Fin 6, (5 / 8 : ℝ)) ≤ 5 / 8 * 6 :=
  lemma_2_1 6 (by norm_num) (by decide) (fun _ => 5 / 8) antitone_const
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ _ _ _ => by norm_num)

/-- The bound above is attained, not merely satisfied. -/
example : (∑ _i : Fin 6, (5 / 8 : ℝ)) = 5 / 8 * 6 := by simp; norm_num

/-- The hypothesis `6 ≤ n` is necessary, because the paper's counterexample at
`n = 4` meets every other hypothesis and breaks the conclusion, so no proof can
drop it.

Every part of that counterexample is checked here, including the triple
condition at all 64 triples; the binding triple is `(0, 2, 2)`, where the
condition holds with equality. -/
example : ∃ a : Fin 4 → ℝ, Antitone a ∧ (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≤ 1) ∧
    (∀ i j k : Fin 4, 4 ≤ (i : ℕ) + (j : ℕ) + (k : ℕ) →
      a i * a j + a j * a k + a k * a i ≤ 5 / 8 * (a i + a j + a k)) ∧
    5 / 8 * 4 < (∑ i, a i) := by
  refine ⟨![1, 3 / 5, 1 / 2, 41 / 100], ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> revert hij <;> norm_num [Fin.le_def]
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num
  · intro i j k hijk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> revert hijk <;> norm_num
  · simp [Fin.sum_univ_four]
    norm_num


end DeepRecursion

/-! ## Node `lemma_2_2`: the asymmetric averaging inequality

Shao's Lemma 2.2, from the proof in arXiv:1206.6139v2, pages 6 to 8. Same
substitution as Lemma 2.1, `x i = 16/5 * a i - 1`, so the hypothesis reads
`x i * y j + y j * z k ≤ 3` and the goal reads `X*Y + Y*Z + Z*X ≤ 3` on the
averages. Write `n = 2m`, and let `X0, X1` be the head and tail halves of the
`x` sum, and likewise for `y` and `z`.

## Shape of the argument

Sum the hypothesis over four index squares rather than the single square Lemma
2.1 uses, and run all four through the same generic `nu_square_bound`:

    M1 : i, j < m ≤ k < 2m      value `X0*Y0 + Y0*Z1 + Z1*X0`, corner `(0,0,m)`
    M2 : i, k < m ≤ j < 2m      value `X0*Z0 + Z0*Y1 + Y1*X0`, corner `(0,m,0)`
    M3 : j, k < m ≤ i < 2m      value `Y0*Z0 + Z0*X1 + X1*Y0`, corner `(m,0,0)`
    M4 : i, j, k all in [m, 2m) value `X1*Y1 + Y1*Z1 + Z1*X1`, corner `(m,m,m)`

The summand `x i * y j + y j * z k + z k * x i` is fully symmetric in its three
values, so M2 and M3 are one lemma with the sequences permuted. A single
`nu_square_bound` therefore covers all four squares. The four values add up to
exactly `Sx*Sy + Sy*Sz + Sz*Sx`, and the three corners of M1, M2, and M3 add up
to exactly `U - W`, where `U` is the quadratic in the pair sums `x 0 + x m` and
`W` is the quadratic in `x m, y m, z m`, so the whole argument reduces to
`U + V - W ≤ 3m² + 9` with `V` the M4 value, and M4 itself supplies Shao's (8).

That reduction is `l22_core`, ten real variables with every summation eliminated,
and it splits five ways, each branch a separate lemma below:

  1. some pair sum of `x 0 + x m, y 0 + y m, z 0 + z m` is negative:
     `l22_U_le_12` gives `U ≤ 12`, and (8) closes it with no slack.
  2. otherwise, all of `X1, Y1, Z1` negative: `l22_case_i`. Both `U` and `V` are
     monotone here, so push each variable to its bound; the shift
     `p = x m - (m - 16/5)` cancels the linear term and leaves `3m² + 33/25`.
  3. not all negative, some pair sum of `X1, Y1, Z1` negative: `l22_V_le_msq`
     gives `V ≤ m²`, against the unconditional `l22_UW_le`. Closing needs
     `2m² ≥ 864/25`, which is exactly where `10 ≤ n` is spent.
  4. all pair sums of `X1, Y1, Z1` nonneg, so `V ≤ m² W`. Split on whether every
     pair sum of `x m, y m, z m` reaches `11/20`, where `l22_case_iv_a` runs
     Shao's (10) to (12) and closes with no slack at all, while `l22_case_iv_b`
     instead bounds `W < 1.3` directly.

Two places in that outline mislead, and the first is the corner of M4, which is
admissible, unlike the other three corners, and is still erased and added back,
because `l22_core` wants `V - W ≤ 3(m²-1)` and the immediate `V ≤ 3m²` is too
weak to supply it.
The other place is `l22_case_iv_b`, which needs `x m + y m ≥ 0`; that is not a
hypothesis of the lemma, and it follows instead from `X1 + Y1 ≥ 0` together with
`X1 ≤ m * x m`, divided through by `m > 0`.

The hypothesis `0 ≤ a i` is used here, unlike in Lemma 2.1, for the lower bound
`-1 ≤ x i` that every box constraint rests on.
-/


/-- The summation step. Sum the hypothesis over one `m × m` index square whose
third index is `m + nu m i j`. The value of that sum is the product expression on
the left, and every triple in the square is admissible except the corner
`(0, 0)`, whose value has to be added back by hand. The lemma is generic in
`u, v, w`, because `lemma_2_2` runs it over four different squares. -/
private theorem nu_square_bound (m : ℕ) (hm : 1 ≤ m) (u v w : ℕ → ℝ)
    (hb : ∀ i j : ℕ, i < m → j < m → ¬ (i = 0 ∧ j = 0) →
      u i * v j + v j * w (m + nu m i j) + w (m + nu m i j) * u i ≤ 3) :
    (∑ i ∈ range m, u i) * (∑ j ∈ range m, v j)
      + (∑ j ∈ range m, v j) * (∑ s ∈ range m, w (m + s))
      + (∑ s ∈ range m, w (m + s)) * (∑ i ∈ range m, u i)
      ≤ 3 * ((m : ℝ) ^ 2 - 1) + (u 0 * v 0 + v 0 * w m + w m * u 0) := by
  classical
  set U0 : ℝ := ∑ i ∈ range m, u i with hU0
  set V0 : ℝ := ∑ j ∈ range m, v j with hV0
  set W1 : ℝ := ∑ s ∈ range m, w (m + s) with hW1
  have hprod : ∑ p ∈ range m ×ˢ range m,
      (u p.1 * v p.2 + v p.2 * w (m + nu m p.1 p.2) + w (m + nu m p.1 p.2) * u p.1)
      = U0 * V0 + V0 * W1 + W1 * U0 := by
    rw [Finset.sum_product]
    have e1 : ∑ i ∈ range m, ∑ j ∈ range m, u i * v j = U0 * V0 := by
      rw [hU0, hV0, Finset.sum_mul_sum]
    have e2 : ∑ i ∈ range m, ∑ j ∈ range m, v j * w (m + nu m i j) = V0 * W1 := by
      rw [Finset.sum_comm]
      have hrowj : ∀ j ∈ range m, ∑ i ∈ range m, v j * w (m + nu m i j) = v j * W1 := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [← Finset.mul_sum]
        congr 1
        have hs : ∀ i ∈ range m, w (m + nu m i j) = w (m + nu m j i) :=
          fun i _ => by rw [nu_symm m i j]
        rw [Finset.sum_congr rfl hs, nu_row m w j hj, ← hW1]
      rw [Finset.sum_congr rfl hrowj, ← Finset.sum_mul, ← hV0]
    have e3 : ∑ i ∈ range m, ∑ j ∈ range m, w (m + nu m i j) * u i = W1 * U0 := by
      have hrowi : ∀ i ∈ range m, ∑ j ∈ range m, w (m + nu m i j) * u i = W1 * u i := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [← Finset.sum_mul, nu_row m w i hi, ← hW1]
      rw [Finset.sum_congr rfl hrowi, ← Finset.mul_sum, ← hU0]
    calc ∑ i ∈ range m, ∑ j ∈ range m,
            (u i * v j + v j * w (m + nu m i j) + w (m + nu m i j) * u i)
        = (∑ i ∈ range m, ∑ j ∈ range m, u i * v j)
          + (∑ i ∈ range m, ∑ j ∈ range m, v j * w (m + nu m i j))
          + (∑ i ∈ range m, ∑ j ∈ range m, w (m + nu m i j) * u i) := by
          simp only [Finset.sum_add_distrib]
      _ = U0 * V0 + V0 * W1 + W1 * U0 := by rw [e1, e2, e3]
  have hmem00 : ((0 : ℕ), (0 : ℕ)) ∈ range m ×ˢ range m := by
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  have herase : ∑ p ∈ (range m ×ˢ range m).erase (0, 0),
      (u p.1 * v p.2 + v p.2 * w (m + nu m p.1 p.2) + w (m + nu m p.1 p.2) * u p.1)
      ≤ 3 * ((m : ℝ) ^ 2 - 1) := by
    have hbound : ∀ p ∈ (range m ×ˢ range m).erase (0, 0),
        u p.1 * v p.2 + v p.2 * w (m + nu m p.1 p.2)
          + w (m + nu m p.1 p.2) * u p.1 ≤ 3 := by
      rintro ⟨i, j⟩ hp
      rw [Finset.mem_erase, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      obtain ⟨hne, hi, hj⟩ := hp
      exact hb i j hi hj (by rintro ⟨rfl, rfl⟩; exact hne rfl)
    have hcard : ((range m ×ˢ range m).erase (0, 0)).card = m * m - 1 := by
      rw [Finset.card_erase_of_mem hmem00, Finset.card_product, Finset.card_range]
    calc ∑ p ∈ (range m ×ˢ range m).erase (0, 0),
            (u p.1 * v p.2 + v p.2 * w (m + nu m p.1 p.2)
              + w (m + nu m p.1 p.2) * u p.1)
        ≤ ∑ _p ∈ (range m ×ˢ range m).erase (0, 0), (3 : ℝ) :=
          Finset.sum_le_sum hbound
      _ = ((m * m - 1 : ℕ) : ℝ) * 3 := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ = 3 * ((m : ℝ) ^ 2 - 1) := by
          have h1 : 1 ≤ m * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
          rw [Nat.cast_sub h1]
          push_cast
          ring
  have hcorner : ∑ p ∈ (range m ×ˢ range m).erase (0, 0),
      (u p.1 * v p.2 + v p.2 * w (m + nu m p.1 p.2) + w (m + nu m p.1 p.2) * u p.1)
      + (u 0 * v 0 + v 0 * w m + w m * u 0) = U0 * V0 + V0 * W1 + W1 * U0 := by
    rw [← hprod, ← Finset.sum_erase_add (range m ×ˢ range m)
      (fun p : ℕ × ℕ => u p.1 * v p.2 + v p.2 * w (m + nu m p.1 p.2)
        + w (m + nu m p.1 p.2) * u p.1) hmem00]
    -- `nu m 0 0` reduces to `0` and `m + 0` to `m`, both definitionally
    congr 1
  linarith [herase, hcorner]


private theorem p12_prod_le {a b : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 11 / 5)
    (hb : -1 ≤ b) (hb' : b ≤ 11 / 5) : a * b ≤ 121 / 25 := by
  have h1 : (0:ℝ) ≤ (11 / 5 - a) * (1 + b) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : (0:ℝ) ≤ (1 + a) * (11 / 5 - b) :=
    mul_nonneg (by linarith) (by linarith)
  linarith [h1, h2]

private theorem p12_prod_le_16 {a b : ℝ} (ha : -4 ≤ a) (ha' : a ≤ 12 / 5)
    (hb : -4 ≤ b) (hb' : b ≤ 12 / 5) : a * b ≤ 16 := by
  have h1 : (0:ℝ) ≤ (12 / 5 - a) * (4 + b) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : (0:ℝ) ≤ (4 + a) * (12 / 5 - b) :=
    mul_nonneg (by linarith) (by linarith)
  linarith [h1, h2]

private theorem p12_U_aux {r s t : ℝ} (hr : -2 ≤ r) (hr' : r ≤ 22 / 5) (hs : -2 ≤ s)
    (hs' : s ≤ 22 / 5) (ht : -2 ≤ t) (_ht' : t ≤ 22 / 5) (hrs : r + s < 0) :
    r * s + s * t + t * r ≤ 12 := by
  have hprod : (0:ℝ) ≤ (-(r + s)) * (t + 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hrs16 : (r - 2) * (s - 2) ≤ 16 :=
    p12_prod_le_16 (by linarith) (by linarith) (by linarith) (by linarith)
  linarith [hprod, hrs16]

private theorem l22_U_le_12 {r s t : ℝ}
    (hr : -2 ≤ r) (hr' : r ≤ 22 / 5) (hs : -2 ≤ s) (hs' : s ≤ 22 / 5)
    (ht : -2 ≤ t) (ht' : t ≤ 22 / 5)
    (hneg : r + s < 0 ∨ s + t < 0 ∨ t + r < 0) :
    r * s + s * t + t * r ≤ 12 := by
  rcases hneg with h | h | h
  · linarith [p12_U_aux hr hr' hs hs' ht ht' h]
  · linarith [p12_U_aux hs hs' ht ht' hr hr' h]
  · linarith [p12_U_aux ht ht' hr hr' hs hs' h]

private theorem l22_UW_le {x0 y0 z0 xm ym zm : ℝ}
    (hx0 : -1 ≤ x0) (hx0' : x0 ≤ 11 / 5) (hy0 : -1 ≤ y0) (hy0' : y0 ≤ 11 / 5)
    (hz0 : -1 ≤ z0) (hz0' : z0 ≤ 11 / 5) (hxm : -1 ≤ xm) (hxm' : xm ≤ 11 / 5)
    (hym : -1 ≤ ym) (hym' : ym ≤ 11 / 5) (hzm : -1 ≤ zm) (hzm' : zm ≤ 11 / 5) :
    ((x0+xm) * (y0+ym) + (y0+ym) * (z0+zm) + (z0+zm) * (x0+xm))
      - (xm * ym + ym * zm + zm * xm) ≤ 1089 / 25 := by
  linarith [p12_prod_le hx0 hx0' hy0 hy0',
            p12_prod_le hx0 hx0' hym hym',
            p12_prod_le hxm hxm' hy0 hy0',
            p12_prod_le hy0 hy0' hz0 hz0',
            p12_prod_le hy0 hy0' hzm hzm',
            p12_prod_le hym hym' hz0 hz0',
            p12_prod_le hz0 hz0' hx0 hx0',
            p12_prod_le hz0 hz0' hxm hxm',
            p12_prod_le hzm hzm' hx0 hx0']


private theorem ci_prod_le {K a b : ℝ} (_hK : 0 ≤ K) (ha : -K ≤ a) (ha' : a ≤ K)
    (hb : -K ≤ b) (hb' : b ≤ K) : a * b ≤ K ^ 2 := by
  have h1 : (K - a) * (K + b) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  have h2 : (K + a) * (K - b) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  linarith [h1, h2]

private theorem l22_case_i {m x0 y0 z0 xm ym zm X1 Y1 Z1 : ℝ} (hm : 4 ≤ m)
    (_hx0 : -1 ≤ x0) (hx0' : x0 ≤ 11 / 5) (_hy0 : -1 ≤ y0) (hy0' : y0 ≤ 11 / 5)
    (_hz0 : -1 ≤ z0) (hz0' : z0 ≤ 11 / 5)
    (hxm : -1 ≤ xm) (hxm' : xm ≤ 11 / 5) (hym : -1 ≤ ym) (hym' : ym ≤ 11 / 5)
    (hzm : -1 ≤ zm) (hzm' : zm ≤ 11 / 5)
    (hX1 : xm - (m - 1) ≤ X1) (hY1 : ym - (m - 1) ≤ Y1) (hZ1 : zm - (m - 1) ≤ Z1)
    (_hXneg : X1 < 0) (hYneg : Y1 < 0) (hZneg : Z1 < 0)
    (_hrs : 0 ≤ (x0 + xm) + (y0 + ym)) (hst : 0 ≤ (y0 + ym) + (z0 + zm))
    (htr : 0 ≤ (z0 + zm) + (x0 + xm)) :
    ((x0+xm) * (y0+ym) + (y0+ym) * (z0+zm) + (z0+zm) * (x0+xm))
      + (X1 * Y1 + Y1 * Z1 + Z1 * X1) - (xm * ym + ym * zm + zm * xm)
      ≤ 3 * m ^ 2 + 33 / 25 := by
  -- Step 1: push each X1 down to its lower bound.
  have hxh : xm - (m - 1) < 0 := by linarith
  have hyh : ym - (m - 1) < 0 := by linarith
  have c1 : (X1 - (xm - (m - 1))) * (Y1 + Z1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have c2 : (Y1 - (ym - (m - 1))) * ((xm - (m - 1)) + Z1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have c3 : (Z1 - (zm - (m - 1))) * ((xm - (m - 1)) + (ym - (m - 1))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hVbound : X1 * Y1 + Y1 * Z1 + Z1 * X1
      ≤ (xm - (m - 1)) * (ym - (m - 1)) + (ym - (m - 1)) * (zm - (m - 1))
        + (zm - (m - 1)) * (xm - (m - 1)) := by
    linarith [c1, c2, c3]
  -- Step 2: push each of x0, y0, z0 up to 11/5.
  have d1 : (0:ℝ) ≤ (11 / 5 - x0) * ((y0+ym) + (z0+zm)) :=
    mul_nonneg (by linarith) (by linarith)
  have d2 : (0:ℝ) ≤ (11 / 5 - y0) * ((z0+zm) + (11 / 5 + xm)) :=
    mul_nonneg (by linarith) (by linarith)
  have d3 : (0:ℝ) ≤ (11 / 5 - z0) * ((11 / 5 + xm) + (11 / 5 + ym)) :=
    mul_nonneg (by linarith) (by linarith)
  have hUbound : (x0+xm) * (y0+ym) + (y0+ym) * (z0+zm) + (z0+zm) * (x0+xm)
      ≤ (11 / 5+xm) * (11 / 5+ym) + (11 / 5+ym) * (11 / 5+zm) + (11 / 5+zm) * (11 / 5+xm) := by
    linarith [d1, d2, d3]
  -- Step 4: bound the shifted product sum.
  have hK : (0:ℝ) ≤ m - 11 / 5 := by linarith
  have q1 : (xm - (m - 16 / 5)) * (ym - (m - 16 / 5)) ≤ (m - 11 / 5) ^ 2 :=
    ci_prod_le hK (by linarith) (by linarith) (by linarith) (by linarith)
  have q2 : (ym - (m - 16 / 5)) * (zm - (m - 16 / 5)) ≤ (m - 11 / 5) ^ 2 :=
    ci_prod_le hK (by linarith) (by linarith) (by linarith) (by linarith)
  have q3 : (zm - (m - 16 / 5)) * (xm - (m - 16 / 5)) ≤ (m - 11 / 5) ^ 2 :=
    ci_prod_le hK (by linarith) (by linarith) (by linarith) (by linarith)
  have hQ : (xm - (m - 16 / 5)) * (ym - (m - 16 / 5)) + (ym - (m - 16 / 5)) * (zm - (m - 16 / 5))
      + (zm - (m - 16 / 5)) * (xm - (m - 16 / 5)) ≤ 3 * (m - 11 / 5) ^ 2 := by linarith
  -- Step 5: finish.  Both sides expand to the same monomials.
  linarith [hUbound, hVbound, hQ]


private theorem vm_key_pos {m X1 Y1 Z1 : ℝ} (hm : 0 ≤ m)
    (_hX : -m ≤ X1) (hY : -m ≤ Y1) (hZ : -m ≤ Z1)
    (hsum : X1 + Y1 < 0) (hx : 0 ≤ X1) (_hzneg : Z1 < 0) :
    X1 * Y1 + Y1 * Z1 + Z1 * X1 ≤ m ^ 2 := by
  have hY1neg : Y1 < 0 := by linarith
  have hxy : X1 * Y1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (le_of_lt hY1neg)
  have h1 : (0:ℝ) ≤ m + Z1 := by linarith
  have h2 : (0:ℝ) ≤ m + X1 + Y1 := by linarith
  nlinarith [mul_nonneg h1 h2, hxy]

private theorem vm_key {m X1 Y1 Z1 : ℝ} (hm : 0 ≤ m)
    (hX : -m ≤ X1) (hY : -m ≤ Y1) (hZ : -m ≤ Z1)
    (hsum : X1 + Y1 < 0) (hnotall : 0 ≤ X1 ∨ 0 ≤ Y1 ∨ 0 ≤ Z1) :
    X1 * Y1 + Y1 * Z1 + Z1 * X1 ≤ m ^ 2 := by
  by_cases hz : 0 ≤ Z1
  · have hzs : Z1 * (X1 + Y1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hz (le_of_lt hsum)
    nlinarith [sq_nonneg (X1 - Y1),
      mul_nonneg (show (0:ℝ) ≤ X1 + Y1 + 2 * m by linarith)
        (show (0:ℝ) ≤ -(X1 + Y1) by linarith), hzs]
  · have hzneg : Z1 < 0 := not_le.mp hz
    rcases hnotall with hx | hy | hzz
    · exact vm_key_pos hm hX hY hZ hsum hx hzneg
    · have := vm_key_pos (m := m) (X1 := Y1) (Y1 := X1) (Z1 := Z1) hm hY hX hZ
        (by linarith) hy hzneg
      linarith [this]
    · linarith

private theorem l22_V_le_msq {m X1 Y1 Z1 : ℝ} (hm : 0 ≤ m)
    (hX : -m ≤ X1) (hY : -m ≤ Y1) (hZ : -m ≤ Z1)
    (hnotall : 0 ≤ X1 ∨ 0 ≤ Y1 ∨ 0 ≤ Z1)
    (hpair : X1 + Y1 < 0 ∨ Y1 + Z1 < 0 ∨ Z1 + X1 < 0) :
    X1 * Y1 + Y1 * Z1 + Z1 * X1 ≤ m ^ 2 := by
  rcases hpair with h | h | h
  · linarith [vm_key (m := m) (X1 := X1) (Y1 := Y1) (Z1 := Z1) hm hX hY hZ h hnotall]
  · have hn : 0 ≤ Y1 ∨ 0 ≤ Z1 ∨ 0 ≤ X1 := by tauto
    linarith [vm_key (m := m) (X1 := Y1) (Y1 := Z1) (Z1 := X1) hm hY hZ hX h hn]
  · have hn : 0 ≤ Z1 ∨ 0 ≤ X1 ∨ 0 ≤ Y1 := by tauto
    linarith [vm_key (m := m) (X1 := Z1) (Y1 := X1) (Z1 := Y1) hm hZ hX hY h hn]


private theorem l22_case_iv_a {m x0 y0 z0 xm ym zm X1 Y1 Z1 : ℝ} (hm : 4 ≤ m)
    (_hx0 : -1 ≤ x0) (hx0' : x0 ≤ 11 / 5) (_hy0 : -1 ≤ y0) (hy0' : y0 ≤ 11 / 5)
    (_hz0 : -1 ≤ z0) (hz0' : z0 ≤ 11 / 5)
    (_hxm : -1 ≤ xm) (_hxm' : xm ≤ 11 / 5) (_hym : -1 ≤ ym) (_hym' : ym ≤ 11 / 5)
    (_hzm : -1 ≤ zm) (_hzm' : zm ≤ 11 / 5)
    (hmx : xm ≤ x0) (hmy : ym ≤ y0) (hmz : zm ≤ z0)
    (hX1 : X1 ≤ m * xm) (hY1 : Y1 ≤ m * ym) (hZ1 : Z1 ≤ m * zm)
    (hXY : 0 ≤ X1 + Y1) (hYZ : 0 ≤ Y1 + Z1) (hZX : 0 ≤ Z1 + X1)
    (h0mm : x0 * ym + ym * zm + zm * x0 ≤ 3)
    (hm0m : xm * y0 + y0 * zm + zm * xm ≤ 3)
    (hmm0 : xm * ym + ym * z0 + z0 * xm ≤ 3)
    (hmmm : xm * ym + ym * zm + zm * xm ≤ 3)
    (hxy : 11 / 20 ≤ xm + ym) (hyz : 11 / 20 ≤ ym + zm) (hzx : 11 / 20 ≤ zm + xm) :
    ((x0+xm) * (y0+ym) + (y0+ym) * (z0+zm) + (z0+zm) * (x0+xm))
      + (X1 * Y1 + Y1 * Z1 + Z1 * X1) - (xm * ym + ym * zm + zm * xm) ≤ 3 * m ^ 2 + 9 := by
  -- Step 1 : V ≤ m^2 * W
  have p1 : 0 ≤ (m * xm - X1) * (Y1 + Z1) := mul_nonneg (by linarith) hYZ
  have p2 : 0 ≤ (m * ym - Y1) * (m * xm + Z1) := mul_nonneg (by linarith) (by linarith)
  have p3 : 0 ≤ (m * zm - Z1) * (m * xm + m * ym) := mul_nonneg (by linarith) (by linarith)
  have hV : X1 * Y1 + Y1 * Z1 + Z1 * X1 ≤ m ^ 2 * (xm * ym + ym * zm + zm * xm) := by
    linarith [p1, p2, p3]
  -- Step 3 : three sign products
  have q1 : (x0 + y0 - 8 * (xm + ym)) * (z0 - zm) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have q2 : (y0 + z0 - 8 * (ym + zm)) * (x0 - xm) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have q3 : (z0 + x0 - 8 * (zm + xm)) * (y0 - ym) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  -- Step 4 : 2*P + 25*W ≤ 81
  have h12 : 2 * (x0 * y0 + y0 * z0 + z0 * x0) + 25 * (xm * ym + ym * zm + zm * xm) ≤ 81 := by
    linarith [q1, q2, q3, h0mm, hm0m, hmm0]
  -- m^2 ≥ 16
  have hm2 : (16:ℝ) ≤ m ^ 2 := by nlinarith [hm, sq_nonneg (m - 4)]
  -- Step 5 : finish
  have hfin : 0 ≤ (m ^ 2 - 27 / 2) * (3 - (xm * ym + ym * zm + zm * xm)) :=
    mul_nonneg (by linarith) (by linarith)
  linarith [hV, h12, hfin, h0mm, hm0m, hmm0]


/-- A product of two reals in `[-1, 11/5]` is at most `121/25`. -/
private theorem ivb_prod_le {a b : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 11 / 5)
    (hb : -1 ≤ b) (hb' : b ≤ 11 / 5) : a * b ≤ 121 / 25 := by
  have h1 : (0:ℝ) ≤ (11 / 5 - a) * (1 + b) := mul_nonneg (by linarith) (by linarith)
  have h2 : (0:ℝ) ≤ (1 + a) * (11 / 5 - b) := mul_nonneg (by linarith) (by linarith)
  linarith [h1, h2]

/-- If `xm + ym` is nonnegative and smaller than `11/20`, the symmetric sum is at
most `13/10`. -/
private theorem ivb_W_small {xm ym zm : ℝ} (_hxm : -1 ≤ xm) (_hxm' : xm ≤ 11 / 5)
    (_hym : -1 ≤ ym) (_hym' : ym ≤ 11 / 5) (_hzm : -1 ≤ zm) (hzm' : zm ≤ 11 / 5)
    (hxy0 : 0 ≤ xm + ym) (hsmall : xm + ym < 11 / 20) :
    xm * ym + ym * zm + zm * xm ≤ 13 / 10 := by
  -- AM-GM: `4 * xm * ym ≤ (xm + ym)^2`.
  have hamgm : 4 * (xm * ym) ≤ (xm + ym) ^ 2 := by linarith [sq_nonneg (xm - ym)]
  -- `(xm + ym)^2 ≤ (11/20) * (xm + ym) < (11/20)^2`.
  have hsqbd : (xm + ym) ^ 2 ≤ (11 / 20) * (xm + ym) :=
    by linarith [mul_nonneg hxy0 (by linarith : (0:ℝ) ≤ 11 / 20 - (xm + ym))]
  -- `zm * (xm + ym) ≤ (11/5) * (xm + ym) < (11/5) * (11/20)`.
  have hz : (0:ℝ) ≤ (11 / 5 - zm) * (xm + ym) := mul_nonneg (by linarith) hxy0
  linarith [hamgm, hsqbd, hz]

private theorem l22_case_iv_b {m x0 y0 z0 xm ym zm X1 Y1 Z1 : ℝ} (hm : 3 ≤ m)
    (hx0 : -1 ≤ x0) (hx0' : x0 ≤ 11 / 5) (hy0 : -1 ≤ y0) (hy0' : y0 ≤ 11 / 5)
    (hz0 : -1 ≤ z0) (hz0' : z0 ≤ 11 / 5)
    (hxm : -1 ≤ xm) (hxm' : xm ≤ 11 / 5) (hym : -1 ≤ ym) (hym' : ym ≤ 11 / 5)
    (hzm : -1 ≤ zm) (hzm' : zm ≤ 11 / 5)
    (hX1 : X1 ≤ m * xm) (hY1 : Y1 ≤ m * ym) (hZ1 : Z1 ≤ m * zm)
    (hXY : 0 ≤ X1 + Y1) (hYZ : 0 ≤ Y1 + Z1) (hZX : 0 ≤ Z1 + X1)
    (h0mm : x0 * ym + ym * zm + zm * x0 ≤ 3)
    (hm0m : xm * y0 + y0 * zm + zm * xm ≤ 3)
    (hmm0 : xm * ym + ym * z0 + z0 * xm ≤ 3)
    (hsmall : xm + ym < 11 / 20 ∨ ym + zm < 11 / 20 ∨ zm + xm < 11 / 20) :
    ((x0+xm) * (y0+ym) + (y0+ym) * (z0+zm) + (z0+zm) * (x0+xm))
      + (X1 * Y1 + Y1 * Z1 + Z1 * X1) - (xm * ym + ym * zm + zm * xm) ≤ 3 * m ^ 2 + 9 := by
  have hmpos : (0:ℝ) < m := by linarith
  -- Step 0: the three pair sums of `xm, ym, zm` are nonnegative.
  have hxy0 : 0 ≤ xm + ym :=
    nonneg_of_mul_nonneg_right (by linarith : (0:ℝ) ≤ m * (xm + ym)) hmpos
  have hyz0 : 0 ≤ ym + zm :=
    nonneg_of_mul_nonneg_right (by linarith : (0:ℝ) ≤ m * (ym + zm)) hmpos
  have hzx0 : 0 ≤ zm + xm :=
    nonneg_of_mul_nonneg_right (by linarith : (0:ℝ) ≤ m * (zm + xm)) hmpos
  -- Step 1: `V ≤ m^2 * W`, by three telescoping nonnegative products.
  have p1 : (0:ℝ) ≤ (m * xm - X1) * (Y1 + Z1) := mul_nonneg (by linarith) hYZ
  have p2 : (0:ℝ) ≤ (m * ym - Y1) * (m * xm + Z1) :=
    mul_nonneg (by linarith) (by linarith)
  have p3 : (0:ℝ) ≤ (m * zm - Z1) * (m * xm + m * ym) :=
    mul_nonneg (by linarith) (by linarith)
  have hV : X1 * Y1 + Y1 * Z1 + Z1 * X1 ≤ m ^ 2 * (xm * ym + ym * zm + zm * xm) := by
    linarith [p1, p2, p3]
  -- Step 2: `W ≤ 13/10`, from `hsmall` and the symmetry of `W`.
  have hW : xm * ym + ym * zm + zm * xm ≤ 13 / 10 := by
    rcases hsmall with h | h | h
    · exact ivb_W_small hxm hxm' hym hym' hzm hzm' hxy0 h
    · linarith [ivb_W_small hym hym' hzm hzm' hxm hxm' hyz0 h]
    · linarith [ivb_W_small hzm hzm' hxm hxm' hym hym' hzx0 h]
  -- Step 3: `P ≤ 363/25`.
  have q1 : x0 * y0 ≤ 121 / 25 := ivb_prod_le hx0 hx0' hy0 hy0'
  have q2 : y0 * z0 ≤ 121 / 25 := ivb_prod_le hy0 hy0' hz0 hz0'
  have q3 : z0 * x0 ≤ 121 / 25 := ivb_prod_le hz0 hz0' hx0 hx0'
  -- Step 4: finish.
  have hm2 : (9:ℝ) ≤ m ^ 2 := by linarith [sq_nonneg (m - 3)]
  have hfin : (0:ℝ) ≤ (m ^ 2 - 1) * (13 / 10 - (xm * ym + ym * zm + zm * xm)) :=
    mul_nonneg (by linarith) (by linarith)
  linarith [hV, hW, q1, q2, q3, hm2, hfin, h0mm, hm0m, hmm0]

/-- Shao's inequality (9), the whole real-arithmetic core of Lemma 2.2. -/
private theorem l22_core {m x0 y0 z0 xm ym zm X1 Y1 Z1 : ℝ} (hm : 5 ≤ m)
    (hx0 : -1 ≤ x0) (hx0' : x0 ≤ 11 / 5) (hy0 : -1 ≤ y0) (hy0' : y0 ≤ 11 / 5)
    (hz0 : -1 ≤ z0) (hz0' : z0 ≤ 11 / 5)
    (hxm : -1 ≤ xm) (hxm' : xm ≤ 11 / 5) (hym : -1 ≤ ym) (hym' : ym ≤ 11 / 5)
    (hzm : -1 ≤ zm) (hzm' : zm ≤ 11 / 5)
    (hmx : xm ≤ x0) (hmy : ym ≤ y0) (hmz : zm ≤ z0)
    (hX1lo : xm - (m - 1) ≤ X1) (hX1hi : X1 ≤ m * xm)
    (hY1lo : ym - (m - 1) ≤ Y1) (hY1hi : Y1 ≤ m * ym)
    (hZ1lo : zm - (m - 1) ≤ Z1) (hZ1hi : Z1 ≤ m * zm)
    (h8 : (X1 * Y1 + Y1 * Z1 + Z1 * X1) - (xm * ym + ym * zm + zm * xm) ≤ 3 * (m ^ 2 - 1))
    (h0mm : x0 * ym + ym * zm + zm * x0 ≤ 3)
    (hm0m : xm * y0 + y0 * zm + zm * xm ≤ 3)
    (hmm0 : xm * ym + ym * z0 + z0 * xm ≤ 3)
    (hmmm : xm * ym + ym * zm + zm * xm ≤ 3) :
    ((x0+xm) * (y0+ym) + (y0+ym) * (z0+zm) + (z0+zm) * (x0+xm))
      + (X1 * Y1 + Y1 * Z1 + Z1 * X1) - (xm * ym + ym * zm + zm * xm) ≤ 3 * m ^ 2 + 9 := by
  by_cases hc1 : (x0+xm) + (y0+ym) < 0 ∨ (y0+ym) + (z0+zm) < 0 ∨ (z0+zm) + (x0+xm) < 0
  · -- some pair sum of `r, s, t` is negative: `U ≤ 12`, and (8) finishes with no slack
    have hU := l22_U_le_12 (r := x0+xm) (s := y0+ym) (t := z0+zm)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) hc1
    linarith [hU, h8]
  · push Not at hc1
    obtain ⟨hrs, hst, htr⟩ := hc1
    by_cases hallneg : X1 < 0 ∧ Y1 < 0 ∧ Z1 < 0
    · -- case (i)
      obtain ⟨hXn, hYn, hZn⟩ := hallneg
      have h := l22_case_i (by linarith) hx0 hx0' hy0 hy0' hz0 hz0' hxm hxm' hym hym'
        hzm hzm' hX1lo hY1lo hZ1lo hXn hYn hZn hrs hst htr
      linarith [h]
    · by_cases hpair : X1 + Y1 < 0 ∨ Y1 + Z1 < 0 ∨ Z1 + X1 < 0
      · -- cases (ii) and (iii): `V ≤ m^2` against the unconditional `U - W ≤ 1089/25`
        have hnotall : 0 ≤ X1 ∨ 0 ≤ Y1 ∨ 0 ≤ Z1 := by
          by_contra hcon
          push Not at hcon
          exact hallneg ⟨hcon.1, hcon.2.1, hcon.2.2⟩
        have hV := l22_V_le_msq (m := m) (by linarith)
          (show -m ≤ X1 by linarith) (show -m ≤ Y1 by linarith)
          (show -m ≤ Z1 by linarith) hnotall hpair
        have hUW := l22_UW_le hx0 hx0' hy0 hy0' hz0 hz0' hxm hxm' hym hym' hzm hzm'
        have hm2 : (25:ℝ) ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 5)]
        linarith [hV, hUW, hm2]
      · push Not at hpair
        obtain ⟨hXY, hYZ, hZX⟩ := hpair
        by_cases hsm : 11 / 20 ≤ xm + ym ∧ 11 / 20 ≤ ym + zm ∧ 11 / 20 ≤ zm + xm
        · -- case (iv)(a)
          exact l22_case_iv_a (by linarith) hx0 hx0' hy0 hy0' hz0 hz0' hxm hxm' hym hym'
            hzm hzm' hmx hmy hmz hX1hi hY1hi hZ1hi hXY hYZ hZX h0mm hm0m hmm0 hmmm
            hsm.1 hsm.2.1 hsm.2.2
        · -- case (iv)(b)
          have hsmall : xm + ym < 11 / 20 ∨ ym + zm < 11 / 20 ∨ zm + xm < 11 / 20 := by
            by_contra hcon
            push Not at hcon
            exact hsm ⟨hcon.1, hcon.2.1, hcon.2.2⟩
          exact l22_case_iv_b (by linarith) hx0 hx0' hy0 hy0' hz0 hz0' hxm hxm' hym hym'
            hzm hzm' hX1hi hY1hi hZ1hi hXY hYZ hZX h0mm hm0m hmm0 hsmall

/-- Moving off `Fin n`. Clamp an antitone `[0,1]`-valued tuple into `x : ℕ → ℝ`
under Shao's substitution `x i = 16/5 * a i - 1`, so that every index side
condition becomes `omega` and the shifted range is `[-1, 11/5]`. `lemma_2_2`
needs this three times over. -/
private theorem l22_clamp {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (hanti : Antitone a)
    (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1) :
    ∃ x : ℕ → ℝ, (∀ (i : ℕ) (h : i < n), x i = 16 / 5 * a ⟨i, h⟩ - 1) ∧
      (∀ i j : ℕ, i ≤ j → x j ≤ x i) ∧ (∀ i : ℕ, -1 ≤ x i) ∧ (∀ i : ℕ, x i ≤ 11 / 5) ∧
      (∑ i ∈ range n, x i) = 16 / 5 * (∑ i, a i) - n := by
  set f : ℕ → Fin n := fun i => ⟨min i (n - 1), by omega⟩ with hfdef
  set x : ℕ → ℝ := fun i => 16 / 5 * a (f i) - 1 with hxdef
  have hfval : ∀ i (h : i < n), f i = ⟨i, h⟩ := by
    intro i h
    apply Fin.val_injective
    simp only [hfdef]
    omega
  have hxlt : ∀ i (h : i < n), x i = 16 / 5 * a ⟨i, h⟩ - 1 := by
    intro i h
    rw [hxdef]
    simp only
    rw [hfval i h]
  refine ⟨x, hxlt, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hle : f i ≤ f j := by simp only [hfdef, Fin.mk_le_mk]; omega
    have := hanti hle
    simp only [hxdef]
    linarith
  · intro i
    have := h0 (f i)
    simp only [hxdef]
    linarith
  · intro i
    have := h1 (f i)
    simp only [hxdef]
    linarith
  · have hs1 : ∑ i : Fin n, x (i : ℕ) = ∑ i ∈ range n, x i :=
      Fin.sum_univ_eq_sum_range (fun i => x i) n
    rw [← hs1]
    have hs2 : ∀ i : Fin n, x (i : ℕ) = 16 / 5 * a i - 1 := fun i => hxlt (i : ℕ) i.isLt
    rw [Finset.sum_congr rfl (fun i _ => hs2 i), Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp

set_option maxHeartbeats 1000000 in
-- The four `nu_square_bound` instances each elaborate a product of six sums, and
-- the closing `linarith` runs over the resulting degree-four monomials.
theorem lemma_2_2 : Statements.Lemma22 := by
  intro n hn10 hev a b c hanti_a hanti_b hanti_c hnn hub hyp A B C hA hB hC
  obtain ⟨m, hm⟩ := hev
  have hm5 : 5 ≤ m := by omega
  have hn0 : 0 < n := by omega
  obtain ⟨x, hxv, hxa, hxl, hxu, hxs⟩ :=
    l22_clamp hn0 a hanti_a (fun i => (hnn i).1) (fun i => (hub i).1)
  obtain ⟨y, hyv, hya, hyl, hyu, hys⟩ :=
    l22_clamp hn0 b hanti_b (fun i => (hnn i).2.1) (fun i => (hub i).2.1)
  obtain ⟨z, hzv, hza, hzl, hzu, hzs⟩ :=
    l22_clamp hn0 c hanti_c (fun i => (hnn i).2.2) (fun i => (hub i).2.2)
  -- the hypothesis in the shifted variables
  have hT : ∀ i j k : ℕ, i < n → j < n → k < n → n ≤ i + j + k →
      x i * y j + y j * z k + z k * x i ≤ 3 := by
    intro i j k hi hj hk hsum
    have h := hyp ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ (by simpa using hsum)
    rw [hxv i hi, hyv j hj, hzv k hk]
    nlinarith [h]
  have hm1 : 1 ≤ m := by omega
  have hnult : ∀ i j : ℕ, i < m → j < m → m + nu m i j < n := by
    intro i j hi hj
    have := nu_lt m i j hi hj
    omega
  -- the four index squares, all through the same generic summation step
  have hM1 : (∑ i ∈ range m, x i) * (∑ j ∈ range m, y j)
      + (∑ j ∈ range m, y j) * (∑ s ∈ range m, z (m + s))
      + (∑ s ∈ range m, z (m + s)) * (∑ i ∈ range m, x i)
      ≤ 3 * ((m : ℝ) ^ 2 - 1) + (x 0 * y 0 + y 0 * z m + z m * x 0) := by
    refine nu_square_bound m hm1 x y z (fun i j hi hj hne => ?_)
    exact hT i j (m + nu m i j) (by omega) (by omega) (hnult i j hi hj)
      (by have := nu_adm m i j hi hj hne; omega)
  have hM2 : (∑ i ∈ range m, x i) * (∑ j ∈ range m, z j)
      + (∑ j ∈ range m, z j) * (∑ s ∈ range m, y (m + s))
      + (∑ s ∈ range m, y (m + s)) * (∑ i ∈ range m, x i)
      ≤ 3 * ((m : ℝ) ^ 2 - 1) + (x 0 * z 0 + z 0 * y m + y m * x 0) := by
    refine nu_square_bound m hm1 x z y (fun i j hi hj hne => ?_)
    have h := hT i (m + nu m i j) j (by omega) (hnult i j hi hj) (by omega)
      (by have := nu_adm m i j hi hj hne; omega)
    linarith [h]
  have hM3 : (∑ i ∈ range m, y i) * (∑ j ∈ range m, z j)
      + (∑ j ∈ range m, z j) * (∑ s ∈ range m, x (m + s))
      + (∑ s ∈ range m, x (m + s)) * (∑ i ∈ range m, y i)
      ≤ 3 * ((m : ℝ) ^ 2 - 1) + (y 0 * z 0 + z 0 * x m + x m * y 0) := by
    refine nu_square_bound m hm1 y z x (fun i j hi hj hne => ?_)
    have h := hT (m + nu m i j) i j (hnult i j hi hj) (by omega) (by omega)
      (by have := nu_adm m i j hi hj hne; omega)
    linarith [h]
  have hM4 : (∑ i ∈ range m, x (m + i)) * (∑ j ∈ range m, y (m + j))
      + (∑ j ∈ range m, y (m + j)) * (∑ s ∈ range m, z (m + s))
      + (∑ s ∈ range m, z (m + s)) * (∑ i ∈ range m, x (m + i))
      ≤ 3 * ((m : ℝ) ^ 2 - 1) + (x m * y m + y m * z m + z m * x m) := by
    refine nu_square_bound m hm1 (fun i => x (m + i)) (fun j => y (m + j)) z
      (fun i j hi hj _ => ?_)
    exact hT (m + i) (m + j) (m + nu m i j) (by omega) (by omega) (hnult i j hi hj)
      (by omega)
  -- the two halves add up
  have hsx : (∑ i ∈ range m, x i) + (∑ s ∈ range m, x (m + s)) = ∑ i ∈ range n, x i := by
    rw [hm]; exact (Finset.sum_range_add (fun i => x i) m m).symm
  have hsy : (∑ i ∈ range m, y i) + (∑ s ∈ range m, y (m + s)) = ∑ i ∈ range n, y i := by
    rw [hm]; exact (Finset.sum_range_add (fun i => y i) m m).symm
  have hsz : (∑ i ∈ range m, z i) + (∑ s ∈ range m, z (m + s)) = ∑ i ∈ range n, z i := by
    rw [hm]; exact (Finset.sum_range_add (fun i => z i) m m).symm
  -- the tail sum is squeezed between `x m - (m-1)` and `m * x m`
  have htail : ∀ w : ℕ → ℝ, (∀ i : ℕ, -1 ≤ w i) → (∀ i j : ℕ, i ≤ j → w j ≤ w i) →
      w m - ((m : ℝ) - 1) ≤ ∑ s ∈ range m, w (m + s) ∧
      (∑ s ∈ range m, w (m + s)) ≤ (m : ℝ) * w m := by
    intro w hwl hwa
    constructor
    · have hmem : (0 : ℕ) ∈ range m := Finset.mem_range.mpr (by omega)
      have hle := Finset.single_le_sum
        (f := fun s => w (m + s) + 1) (fun s _ => by linarith [hwl (m + s)]) hmem
      have hsplit : ∑ s ∈ range m, (w (m + s) + 1)
          = (∑ s ∈ range m, w (m + s)) + (m : ℝ) := by
        rw [Finset.sum_add_distrib]; simp
      rw [hsplit] at hle
      have h0 : w (m + 0) + 1 ≤ (∑ s ∈ range m, w (m + s)) + (m : ℝ) := hle
      simp only [Nat.add_zero] at h0
      linarith
    · calc ∑ s ∈ range m, w (m + s) ≤ ∑ _s ∈ range m, w m :=
            Finset.sum_le_sum (fun s _ => hwa m (m + s) (Nat.le_add_right m s))
        _ = (m : ℝ) * w m := by simp [mul_comm]
  obtain ⟨hX1lo, hX1hi⟩ := htail x hxl hxa
  obtain ⟨hY1lo, hY1hi⟩ := htail y hyl hya
  obtain ⟨hZ1lo, hZ1hi⟩ := htail z hzl hza
  have hmn : m < n := by omega
  have hm5R : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm5
  -- the real-arithmetic core
  have hcore := l22_core hm5R (hxl 0) (hxu 0) (hyl 0) (hyu 0) (hzl 0) (hzu 0)
    (hxl m) (hxu m) (hyl m) (hyu m) (hzl m) (hzu m)
    (hxa 0 m (Nat.zero_le m)) (hya 0 m (Nat.zero_le m)) (hza 0 m (Nat.zero_le m))
    hX1lo hX1hi hY1lo hY1hi hZ1lo hZ1hi (by linarith [hM4])
    (hT 0 m m hn0 hmn hmn (by omega)) (hT m 0 m hmn hn0 hmn (by omega))
    (hT m m 0 hmn hmn hn0 (by omega)) (hT m m m hmn hmn hmn (by omega))
  -- the four squares reassemble into the product of the full sums
  have hkey : (∑ i ∈ range n, x i) * (∑ i ∈ range n, y i)
      + (∑ i ∈ range n, y i) * (∑ i ∈ range n, z i)
      + (∑ i ∈ range n, z i) * (∑ i ∈ range n, x i) ≤ 12 * (m : ℝ) ^ 2 := by
    rw [← hsx, ← hsy, ← hsz]
    linarith [hM1, hM2, hM3, hcore]
  -- back to the averages
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnR : ((n : ℕ) : ℝ) = 2 * (m : ℝ) := by rw [hm]; push_cast; ring
  have hAn : (∑ i, a i) = (n : ℝ) * A := by rw [hA]; field_simp
  have hBn : (∑ i, b i) = (n : ℝ) * B := by rw [hB]; field_simp
  have hCn : (∑ i, c i) = (n : ℝ) * C := by rw [hC]; field_simp
  have hSxA : (∑ i ∈ range n, x i) = (n : ℝ) * (16 / 5 * A - 1) := by
    rw [hxs, hAn]; ring
  have hSyB : (∑ i ∈ range n, y i) = (n : ℝ) * (16 / 5 * B - 1) := by
    rw [hys, hBn]; ring
  have hSzC : (∑ i ∈ range n, z i) = (n : ℝ) * (16 / 5 * C - 1) := by
    rw [hzs, hCn]; ring
  have hexp : (∑ i ∈ range n, x i) * (∑ i ∈ range n, y i)
      + (∑ i ∈ range n, y i) * (∑ i ∈ range n, z i)
      + (∑ i ∈ range n, z i) * (∑ i ∈ range n, x i)
      = (n : ℝ) ^ 2 * ((256 / 25) * (A * B + B * C + C * A)
          - (32 / 5) * (A + B + C) + 3) := by
    rw [hSxA, hSyB, hSzC]; ring
  have h12 : (12 : ℝ) * (m : ℝ) ^ 2 = 3 * (n : ℝ) ^ 2 := by rw [hnR]; ring
  by_contra hcon
  push Not at hcon
  have hnsq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hgap : (0 : ℝ) < (n : ℝ) ^ 2 * ((A * B + B * C + C * A) - 5 / 8 * (A + B + C)) :=
    mul_pos hnsq (by linarith)
  linarith [hkey, hexp, h12, hgap]


/-! ### Anti-vacuity for `lemma_2_2`

Three checks sit below, of which the first two apply the proved theorem to a
real input and so also confirm that it accepts one, while the third records
where the hypothesis `10 ≤ n` is spent.
-/

/-- The hypothesis class is inhabited at `n = 10`, and the bound is attained
there rather than merely satisfied, so the node is neither vacuous nor slack.

At the constant `5/8` in all three sequences the triple condition reads
`3 * (5/8)^2 ≤ 5/8 * (3 * 5/8)`, and both sides are `75/64`. The three averages
are all `5/8`, and the conclusion is again `75/64 ≤ 75/64`. -/
example : (5 / 8 : ℝ) * (5 / 8) + (5 / 8) * (5 / 8) + (5 / 8) * (5 / 8)
    ≤ 5 / 8 * (5 / 8 + 5 / 8 + 5 / 8) :=
  lemma_2_2 10 (by norm_num) (by decide)
    (fun _ => 5 / 8) (fun _ => 5 / 8) (fun _ => 5 / 8)
    antitone_const antitone_const antitone_const
    (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    (fun _ _ _ _ => by norm_num)
    (5 / 8) (5 / 8) (5 / 8) (by norm_num) (by norm_num) (by norm_num)

/-- The three sequences really may differ, and that extra freedom is what
Lemma 2.2 offers over Lemma 2.1. Here `c` is the constant `1/2` while `a` and `b` are `5/8`, so the
hypothesis holds strictly at `65/64 < 70/64` and the conclusion holds strictly
as well; a witness with all three sequences equal could not have shown it. -/
example : (5 / 8 : ℝ) * (5 / 8) + (5 / 8) * (1 / 2) + (1 / 2) * (5 / 8)
    ≤ 5 / 8 * (5 / 8 + 5 / 8 + 1 / 2) :=
  lemma_2_2 10 (by norm_num) (by decide)
    (fun _ => 5 / 8) (fun _ => 5 / 8) (fun _ => 1 / 2)
    antitone_const antitone_const antitone_const
    (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    (fun _ => ⟨by norm_num, by norm_num, by norm_num⟩)
    (fun _ _ _ _ => by norm_num)
    (5 / 8) (5 / 8) (1 / 2) (by norm_num) (by norm_num) (by norm_num)

/-- Where `10 ≤ n` is spent, as a plain arithmetic fact. Cases (ii) and (iii)
close by `l22_UW_le` against `l22_V_le_msq`, which needs
`1089/25 + m ^ 2 ≤ 3 * m ^ 2 + 9`, that is `864/25 ≤ 2 * m ^ 2`. At `m = 4`, so
`n = 8`, that fails; at `m = 5`, so `n = 10`, it holds. No other case in
`l22_core` needs more than `m ≥ 4`. -/
example : ¬ (864 / 25 ≤ 2 * (4 : ℝ) ^ 2) ∧ (864 / 25 ≤ 2 * (5 : ℝ) ^ 2) := by
  norm_num


/-! ## Corollary 1.5 from Proposition 1.4

Corollary 1.5 is the `f = 1_A` case of Proposition 1.4, and that specialization
only needs the indicator function of `A`, so it is discharged here
rather than at the end of the file; with `prop_1_4` in hand the node is the
single line

    theorem cor_1_5 : Statements.Cor15 := cor15_of_prop14 prop_1_4

Keeping the specialization apart from the induction makes plain that `prop_1_4`
has to deliver the weighted statement, from which the set statement then
follows.
-/

/-- `Cor15` is the `f = 1_A` case of `Prop14`. Feeding in the indicator of `A`
makes the sum over the units equal `|A|`, because `A` sits inside the units, and
the product condition `0 < f a₁ * f a₂ * f a₃` then says that all three
indicator values are `1`, which is membership in `A`. The strength condition
`3/2 < f a₁ + f a₂ + f a₃` plays no part here, since it is what the induction
inside `Prop14` consumes. -/
private theorem cor15_of_prop14 : Statements.Prop14 → Statements.Cor15 := by
  classical
  intro H m inst hodd hsq A hAU hcard x
  set f : ZMod m → ℝ := fun y => if y ∈ A then 1 else 0 with hf
  have hf0 : ∀ y, 0 ≤ f y := by
    intro y; rw [hf]; dsimp only; split <;> norm_num
  have hf1 : ∀ y, f y ≤ 1 := by
    intro y; rw [hf]; dsimp only; split <;> norm_num
  have hfilter : (Statements.U m).filter (fun y => y ∈ A) = A := by
    rw [Finset.filter_mem_eq_inter]
    exact Finset.inter_eq_right.mpr hAU
  have hsum : (∑ y ∈ Statements.U m, f y) = (A.card : ℝ) := by
    rw [hf]
    rw [Finset.sum_boole, hfilter]
  have hdens : (5 : ℝ) / 8 * (Nat.totient m) < ∑ y ∈ Statements.U m, f y := by
    rw [hsum]
    have h : (5 * Nat.totient m : ℝ) < (8 * A.card : ℝ) := by exact_mod_cast hcard
    linarith
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hxsum, hpos, -⟩ := H m hodd hsq f hf0 hf1 hdens x
  have hmem : ∀ y, 0 < f y → y ∈ A := by
    intro y hy
    by_contra hc
    rw [hf] at hy
    simp only [if_neg hc] at hy
    exact lt_irrefl 0 hy
  have h1 : 0 < f a₁ := by
    rcases (hf0 a₁).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hpos; simp at hpos
  have h2 : 0 < f a₂ := by
    rcases (hf0 a₂).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hpos; simp at hpos
  have h3 : 0 < f a₃ := by
    rcases (hf0 a₃).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hpos; simp at hpos
  exact ⟨a₁, hmem a₁ h1, a₂, hmem a₂ h2, a₃, hmem a₃ h3, hxsum⟩

/-- Anti-vacuity for `cor15_of_prop14`. The reduction is not a statement about
an empty hypothesis class, since at `m = 15` the whole unit group has
`8 = phi 15` elements and clears the density condition `5 * 8 < 8 * 8`. -/
example : (5 * Nat.totient 15 < 8 * (Statements.U 15).card) := by
  rw [card_U 15]
  decide +kernel


/-! ## Node `divisor_reduction`

Shao asserts this step in one sentence: "if the result holds for
`m`, then it also holds for any `m'` dividing `m`". The construction below is a
reconstruction, since the paper supplies none.

Fix `m ∣ M`, let `ρ : ZMod M →+* ZMod m` be the reduction and `π` its
restriction to units, and feed `Prop14At M` the pullback `G b = g (ρ b)`.
Because `π` is a surjective homomorphism of finite groups, all of its fibers
share one size `c`, so summing over the `φ m` fibers gives both `φ M = c * φ m`
and `Σ_{U M} G = c * Σ_{U m} g`; the factor `c` then cancels exactly, the
density hypothesis transports without spending slack, and strictness survives.
Coming back down, `ρ` is surjective, maps units to units, and commutes with
the triple sum, so the two numeric conclusions are literally the same terms.

Two places in that construction mislead, and the first is that the fiber
statement is about `U M` rather than about the full preimage `ρ⁻¹(U m)`, which
is strictly larger for most divisor pairs;
at `m = 3` and `M = 15`, for instance, the non-units `5` and `10` reduce to the
units `2` and `1`. And this step does not need `Odd`, `Squarefree`, or `m`
coprime to `M / m`, since divisibility alone is enough, with the oddness and
the squarefreeness entering later in `prop14_of_main`.

The reduction is insensitive to the constants `5/8` and `3/2`, and any other
pair of constants would reduce in exactly the same way.
-/

/-! ## The unit `Finset` as the image of the unit group -/

/-- `Statements.U m` is the image of the unit group under `Units.val`. The same
step is already inlined in `card_U`, and it is factored out here because
`divisor_reduction` needs the sum version of it as well as the card version. -/
private theorem U_eq_image (m : ℕ) [NeZero m] :
    Statements.U m = Finset.univ.image (Units.val : (ZMod m)ˣ → ZMod m) := by
  classical
  ext x
  constructor
  · intro hx
    have hu : IsUnit x := by simpa [Statements.U] using hx
    obtain ⟨u, hu⟩ := hu
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, hu⟩
  · intro hx
    obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hx
    have : IsUnit x := hu ▸ u.isUnit
    simpa [Statements.U] using this

/-- Summing over `Statements.U m` is summing over the unit group. -/
private theorem sum_U (m : ℕ) [NeZero m] (f : ZMod m → ℝ) :
    ∑ x ∈ Statements.U m, f x = ∑ u : (ZMod m)ˣ, f (u : ZMod m) := by
  classical
  rw [U_eq_image m,
    Finset.sum_image (by intro a _ b _ h; exact Units.val_injective h)]

/-! ## The fiber count, in the only form the proof needs -/

/-- For a surjective homomorphism of finite groups, summing a pulled-back
function multiplies the sum by the common fiber size. All fibers are cosets of
the kernel, so `MonoidHom.card_fiber_eq_of_mem_range` gives each of them the
size of the fiber over `1`, and `Finset.sum_fiberwise` does the bookkeeping from
there.

Taking `F = 1` gives the card identity `|G| = c * |H|`, and that is the route by
which `φ M = c * φ m` is obtained below. The quotient `|G| / |H|` is never
formed. -/
private theorem sum_comp_surj {G H : Type*} [Group G] [Group H] [Fintype G]
    [Fintype H] [DecidableEq H] (π : G →* H) (hsurj : Function.Surjective π)
    (F : H → ℝ) :
    ∑ u : G, F (π u) = (#{u : G | π u = 1} : ℝ) * ∑ v : H, F v := by
  classical
  have hconst : ∀ v : H, (#{u : G | π u = v}) = #{u : G | π u = 1} :=
    fun v => MonoidHom.card_fiber_eq_of_mem_range π (hsurj v) ⟨1, map_one π⟩
  rw [← Finset.sum_fiberwise (Finset.univ : Finset G) (fun u => π u)
    (fun u => F (π u))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro v _
  rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2])]
  rw [Finset.sum_const, nsmul_eq_mul, hconst v]

/-! ## Node `divisor_reduction` -/

/-- Node `divisor_reduction`. `Prop14At` at a modulus `M` implies `Prop14At` at
every divisor `m` of `M`, by the construction set out in the section header
above. -/
theorem divisor_reduction : Statements.DivisorReduction := by
  classical
  intro m M _ _ hdvd hM g hg0 hg1 hsum x
  set ρ : ZMod M →+* ZMod m := ZMod.castHom hdvd (ZMod m) with hρ
  set π : (ZMod M)ˣ →* (ZMod m)ˣ := ZMod.unitsMap hdvd with hπ
  have hsurj : Function.Surjective π := ZMod.unitsMap_surjective hdvd
  set c : ℕ := #{u : (ZMod M)ˣ | π u = 1} with hc
  set G : ZMod M → ℝ := fun b => g (ρ b) with hG
  -- `ρ` on values agrees with `π` on units
  have hval : ∀ u : (ZMod M)ˣ, ρ (u : ZMod M) = ((π u : (ZMod m)ˣ) : ZMod m) := by
    intro u; rw [hπ, hρ]; exact (ZMod.unitsMap_val hdvd u).symm
  -- the sum identity
  have hsumid : ∑ b ∈ Statements.U M, G b = (c : ℝ) * ∑ a ∈ Statements.U m, g a := by
    rw [sum_U M G, sum_U m g]
    have h : ∀ u : (ZMod M)ˣ, G (u : ZMod M) = g ((π u : (ZMod m)ˣ) : ZMod m) := by
      intro u; rw [hG]; simp only []; rw [hval u]
    rw [Finset.sum_congr rfl (fun u _ => h u)]
    exact sum_comp_surj π hsurj (fun v => g (v : ZMod m))
  -- the card identity `φ M = c * φ m`, the same fact at `F = 1`
  have hcard : Nat.totient M = c * Nat.totient m := by
    have h1 : ∑ _u : (ZMod M)ˣ, (1 : ℝ) = (c : ℝ) * ∑ _v : (ZMod m)ˣ, (1 : ℝ) :=
      sum_comp_surj π hsurj (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ZMod.card_units_eq_totient] at h1
    exact_mod_cast h1
  -- the fiber size is positive, because `φ M` is
  have hMpos : 0 < Nat.totient M :=
    Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  -- the hypotheses of `Prop14At M`
  have hG0 : ∀ b, 0 ≤ G b := fun b => hg0 _
  have hG1 : ∀ b, G b ≤ 1 := fun b => hg1 _
  have hsum' : (5 : ℝ) / 8 * (Nat.totient M) < ∑ b ∈ Statements.U M, G b := by
    rw [hsumid, hcard]
    push_cast
    nlinarith [hsum]
  -- lift the target, apply, push the answer back down
  obtain ⟨y, hy⟩ := ZMod.castHom_surjective (m := m) (n := M) hdvd x
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, hadd, hprod, hsum3⟩ := hM G hG0 hG1 hsum' y
  have hu : ∀ b ∈ Statements.U M, ρ b ∈ Statements.U m := by
    intro b hb
    have : IsUnit b := by simpa [Statements.U] using hb
    simpa [Statements.U] using this.map ρ
  refine ⟨ρ b₁, hu _ hb₁, ρ b₂, hu _ hb₂, ρ b₃, hu _ hb₃, ?_, hprod, hsum3⟩
  rw [← map_add, ← map_add, hadd, hρ, hy]

/-! ## Anti-vacuity for `divisor_reduction`

A clean audit says the implication follows from standard axioms, and it does
not say whether either side is ever true. The witnesses below claim more
than that the hypothesis class is nonempty, since the last of them is an actual
modus ponens whose hypothesis `Prop14At 3` is proved outright rather than
assumed.
-/

/-- The reduction is an implication between two statements about different
moduli, so it is not a disguised identity. -/
example : Statements.Prop14At 15 → Statements.Prop14At 3 :=
  divisor_reduction 3 15 (by norm_num)

/-- The fiber constant of the proof is a real number other than `1`, so the
reduction does real arithmetic rather than renaming. At `m = 3` and
`M = 15` it is `φ 15 / φ 3 = 8 / 2 = 4`, exactly the `c` the proof
constructs. -/
example :
    #{u : (ZMod 15)ˣ | ZMod.unitsMap (show (3 : ℕ) ∣ 15 by norm_num) u = 1} = 4 := by
  decide

/-- The units mod 3, listed, by the same `isUnit_iff_exists_inv` step as `U15`. -/
private theorem U3 : Statements.U 3 = ({1, 2} : Finset (ZMod 3)) := by
  ext x
  simp only [Statements.U, Finset.mem_filter, Finset.mem_univ, true_and,
    isUnit_iff_exists_inv]
  revert x
  decide

/-- `Prop14At 3` holds outright. The density hypothesis forces
`g 1 + g 2 > 5/4` with both values at most `1`, so both values lie above `1/4`
and the larger of the two lies above `5/8`. The triples `(1,1,1)` and `(2,2,2)`
hit `0`, the triple `(1,1,2)` hits `1`, and the triple `(1,2,2)` hits `2`, and
in each of those cases the sum of the three values exceeds `3/2`. -/
private theorem prop14At_three : Statements.Prop14At 3 := by
  intro g hg0 hg1 hsum y
  have hne : (1 : ZMod 3) ≠ 2 := by decide
  rw [U3, Finset.sum_pair hne] at hsum
  have ht : Nat.totient 3 = 2 := by decide
  rw [ht] at hsum
  push_cast at hsum
  have h1le : g 1 ≤ 1 := hg1 1
  have h2le : g 2 ≤ 1 := hg1 2
  have h1pos : 0 < g 1 := by linarith
  have h2pos : 0 < g 2 := by linarith
  have hm1 : (1 : ZMod 3) ∈ Statements.U 3 := by rw [U3]; decide
  have hm2 : (2 : ZMod 3) ∈ Statements.U 3 := by rw [U3]; decide
  have hy : y = 0 ∨ y = 1 ∨ y = 2 := by revert y; decide
  rcases hy with rfl | rfl | rfl
  · rcases le_total (g 1) (g 2) with h | h
    · exact ⟨2, hm2, 2, hm2, 2, hm2, by decide,
        mul_pos (mul_pos h2pos h2pos) h2pos, by linarith⟩
    · exact ⟨1, hm1, 1, hm1, 1, hm1, by decide,
        mul_pos (mul_pos h1pos h1pos) h1pos, by linarith⟩
  · exact ⟨1, hm1, 1, hm1, 2, hm2, by decide,
      mul_pos (mul_pos h1pos h1pos) h2pos, by linarith⟩
  · exact ⟨1, hm1, 2, hm2, 2, hm2, by decide,
      mul_pos (mul_pos h1pos h2pos) h2pos, by linarith⟩

/-- The reduction fires on `Prop14At 3` above, which is proved rather than
hypothesized, transported down the divisibility `1 ∣ 3`, so `divisor_reduction`
is not vacuously true through an unsatisfiable premise. -/
example : Statements.Prop14At 1 :=
  divisor_reduction 1 3 (one_dvd 3) prop14At_three

/-! ## The `WLOG 15 divides m` step of Proposition 1.4

This step comes ahead of the node it serves, for the same reason as the section
above, in that it is self-contained, it only needs
`divisor_reduction`, and it narrows what remains of Proposition 1.4 down to the
single case `15 divides M`.
-/

private theorem lcm_ne_zero {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : Nat.lcm a b ≠ 0 := by
  intro h
  rcases Nat.lcm_eq_zero_iff.mp h with h' | h'
  · exact ha h'
  · exact hb h'

private theorem odd_lcm {m : ℕ} (hm : Odd m) : Odd (Nat.lcm m 15) := by
  rw [Nat.odd_iff] at hm ⊢
  by_contra hc
  have hdvd : 2 ∣ Nat.lcm m 15 := by omega
  have h1 : Nat.lcm m 15 ∣ m * 15 :=
    Nat.lcm_dvd (dvd_mul_right m 15) (dvd_mul_left 15 m)
  have h2 : 2 ∣ m * 15 := dvd_trans hdvd h1
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h <;> omega

private theorem squarefree_lcm {m : ℕ} (hm0 : m ≠ 0) (hm : Squarefree m) :
    Squarefree (Nat.lcm m 15) := by
  have h15 : Squarefree 15 := by decide +kernel
  have hne : Nat.lcm m 15 ≠ 0 := lcm_ne_zero hm0 (by norm_num)
  rw [Nat.squarefree_iff_factorization_le_one hne]
  intro p
  rw [Nat.factorization_lcm hm0 (by norm_num : (15 : ℕ) ≠ 0)]
  simp only [Finsupp.sup_apply, sup_le_iff]
  constructor
  · exact (Nat.squarefree_iff_factorization_le_one hm0).mp hm p
  · exact (Nat.squarefree_iff_factorization_le_one (by norm_num)).mp h15 p

/-- The `WLOG 15 ∣ m` reduction of Proposition 1.4.

The paper opens the proof of Proposition 1.4 with one sentence: "First note that
if the result holds for `m`, then it also holds for any `m'` dividing `m`. Hence
we may assume that `15|m`." That sentence is exactly `divisor_reduction` applied
at `M = lcm m 15`, together with the three closure facts proved above, that the
lcm of an odd number with `15` is odd, that the lcm of two squarefree numbers is
squarefree, and that `15` divides it.

The whole content of Proposition 1.4 is therefore the case `15 ∣ M`, and that
case is the hypothesis `Hmain`. -/
private theorem prop14_of_main (HDR : Statements.DivisorReduction)
    (Hmain : ∀ (M : ℕ), ∀ _ : NeZero M, Odd M → Squarefree M → 15 ∣ M →
      Statements.Prop14At M) :
    Statements.Prop14 := by
  intro m inst hodd hsq
  have hm0 : m ≠ 0 := NeZero.ne m
  have hne : Nat.lcm m 15 ≠ 0 := lcm_ne_zero hm0 (by norm_num)
  have instM : NeZero (Nat.lcm m 15) := ⟨hne⟩
  exact HDR m (Nat.lcm m 15) (Nat.dvd_lcm_left m 15)
    (Hmain (Nat.lcm m 15) instM (odd_lcm hodd) (squarefree_lcm hm0 hsq)
      (Nat.dvd_lcm_right m 15))

/-! ## A dictionary for Proposition 3.1

Proposition 3.1 opens both of its cases by sorting the values of `f` on the
units into decreasing order and then reading three level sets off the sorted
tuple, and `exists_antitone_rearrangement` is that step, stated once for any
finite set. It comes ahead of the node it serves because it connects the two
averaging lemmas to `cd_chowla`, which speak different languages; the averaging
lemmas speak about an antitone `Fin n -> R`, `cd_chowla` speaks about `Finset`
cardinalities, and the counting clause of the rearrangement translates one into
the other.
-/

/-- The rearrangement dictionary.

Shao's Proposition 3.1 opens both of its cases with "let `a₀ ≥ a₁ ≥ ... ≥ a_{p-2}`
be the `p-1` values of `f` in decreasing order", and this lemma is that sentence.

Given any finite `S` and any real `f`, it produces an antitone tuple `a` indexed
by `Fin S.card` taking exactly the values of `f` on `S`, with the same sum and
with the counting fact the proof goes on to use, that at least `i+1` elements of
`S` satisfy `f x ≥ a i`. That last clause is what feeds Cauchy-Davenport-Chowla,
through `|I| + |J| + |K| ≥ (i+1) + (j+1) + (k+1) ≥ p + 2`. -/
private theorem exists_antitone_rearrangement {α : Type*}
    (S : Finset α) (f : α → ℝ) :
    ∃ a : Fin S.card → ℝ, Antitone a ∧
      (∀ i, ∃ x ∈ S, f x = a i) ∧
      (∑ i, a i) = (∑ x ∈ S, f x) ∧
      (∀ i : Fin S.card, (i : ℕ) + 1 ≤ (S.filter (fun x => a i ≤ f x)).card) := by
  classical
  set N := S.card with hN
  set e : Fin N ≃ S := (S.equivFin).symm with he
  set g : Fin N → ℝ := fun i => f (e i : α) with hg
  set σ := Tuple.sort g with hsig
  have hmono : Monotone (g ∘ σ) := Tuple.monotone_sort g
  set a : Fin N → ℝ := fun i => g (σ (Fin.rev i)) with ha
  set w : Fin N → α := fun i => (e (σ (Fin.rev i)) : α) with hw
  have hwS : ∀ i, w i ∈ S := fun i => (e (σ (Fin.rev i))).2
  have hfw : ∀ i, f (w i) = a i := fun i => rfl
  have hwinj : Function.Injective w := by
    intro i j hij
    have h2 : e (σ (Fin.rev i)) = e (σ (Fin.rev j)) := Subtype.ext hij
    exact Fin.rev_injective (σ.injective (e.injective h2))
  have hanti : Antitone a := fun i j hij => hmono (Fin.rev_le_rev.mpr hij)
  refine ⟨a, hanti, fun i => ⟨w i, hwS i, hfw i⟩, ?_, ?_⟩
  · calc (∑ i, a i) = ∑ i, g ((Fin.revPerm.trans σ) i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp [ha, Equiv.trans_apply]
      _ = ∑ i, g i := Equiv.sum_comp _ g
      _ = ∑ i : Fin N, f ((e i : α)) := rfl
      _ = ∑ s : S, f (s : α) := Equiv.sum_comp e (fun s : S => f (s : α))
      _ = ∑ x ∈ S, f x := Finset.sum_coe_sort S f
  · intro i
    have hsub : (Finset.Iic i).image w ⊆ S.filter (fun x => a i ≤ f x) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_Iic] at hx
      obtain ⟨l, hl, rfl⟩ := hx
      refine Finset.mem_filter.mpr ⟨hwS l, ?_⟩
      rw [hfw l]
      exact hanti hl
    have hcard : ((Finset.Iic i).image w).card = (i : ℕ) + 1 := by
      rw [Finset.card_image_of_injective _ hwinj, Fin.card_Iic]
    calc (i : ℕ) + 1 = ((Finset.Iic i).image w).card := hcard.symm
      _ ≤ (S.filter (fun x => a i ≤ f x)).card := Finset.card_le_card hsub

/-- Anti-vacuity for `exists_antitone_rearrangement`. The lemma says something
at a concrete nonempty `S`, and the sum really is preserved, since at
`S = {1,2,3}` under the identity the rearranged tuple is antitone and sums
to `6`. -/
example : ∃ a : Fin ({1, 2, 3} : Finset ℕ).card → ℝ, Antitone a ∧ (∑ i, a i) = 6 := by
  obtain ⟨a, h1, -, h3, -⟩ :=
    exists_antitone_rearrangement ({1, 2, 3} : Finset ℕ) (fun n => (n : ℝ))
  refine ⟨a, h1, ?_⟩
  rw [h3]
  norm_num

/-!
## Node `prop_3_2`: Shao's Proposition 3.2, the weighted case `m = 15`

Shao, arXiv:1206.6139v2, Proposition 3.2. Given `f₁, f₂, f₃ : ZMod 15 → [0,1]`
with unit-sums `F₁, F₂, F₃` satisfying `F₁F₂ + F₂F₃ + F₃F₁ > 5(F₁+F₂+F₃)`, every
`x : ZMod 15` is a sum of three units on which the product is positive and the
values add to more than `3/2`.

## Shape of the argument

Let `Aᵢ` be the support of `fᵢ` inside `U 15` and `nᵢ = |Aᵢ| ≤ 8`, sort the
values of `fᵢ` on `Aᵢ` into a decreasing tuple extended by zero to `ℕ → ℝ`, and
call that tuple `gᵢ`. Then `Fᵢ = ∑_{k < nᵢ} gᵢ k` and `Fᵢ ≤ nᵢ`, so `mono17`
upgrades Shao's (16) on the `F`s to his (17) on the `n`s.

The argument then splits on Shao's dichotomy at the index set
`J = {(k₁,k₂,k₃) : kᵢ < nᵢ and T(k₁+1,k₂+1,k₃+1) > 0}`, where
`T x y z = xy+yz+zx-5(x+y+z)`.

In Case A some `J` triple has `g₁k₁ + g₂k₂ + g₃k₃ > 3/2`. Take
`Bᵢ = Aᵢ.filter (gᵢ kᵢ ≤ fᵢ ·)`; the counting clause of the rearrangement gives
`|Bᵢ| ≥ kᵢ + 1`, and `J` is an up-set by `upset3`, so `T(|B₁|,|B₂|,|B₃|) > 0`
and `lemma_2_3` lands `aᵢ ∈ Bᵢ` with `a₁+a₂+a₃ = x`. Every `fᵢ aᵢ ≥ gᵢ kᵢ`, so
the three values add to more than `3/2`. A `Bᵢ` strictly larger than `kᵢ+1`
is harmless here, so no subset of exactly that size ever has to be built.

In Case B no `J` triple exceeds `3/2`, which is Shao's constraint family (19),
expressed here by the predicate `Con`, and `caseB` contradicts (16) outright from
it. Six-fold symmetry cuts the work down to `caseB_sorted`, `cases34` enumerates
the 34 admissible sorted triples, and each triple is closed by one linear
program together with one of the four endgame quadratics `E1` to `E4`.

## The 36 linear programs

Shao says "the maximum of `S` can be found using a linear programming
algorithm" and tabulates the answers. Here each case has an explicit dual
(Farkas) certificate, and the certificate is spent as the list of `J` rows to
instantiate, after which `linarith` reconstructs the multipliers itself,
including the half-integral ones at `(4,7,8)`, `(5,6,8)`, `(6,8,8)`, and
`(7,7,8)`, where no integral certificate exists. Monotonicity of `gᵢ` is
provably redundant in every one of the 36 programs and is therefore never passed
to `linarith`, though it is still needed earlier, both to build the `gᵢ` and to
run Case A.

The count is 36 rather than the paper's 34, because `(4,5,8)` and `(4,8,8)` each
split, on `F₁+F₂ ≥ 8` and on `F₁ ≥ 3` respectively, with the branch re-solved
once the extra row is added; Shao states both of those splits himself.

The certificates were produced by an exact rational simplex and re-verified
coefficientwise, on nonnegativity, on `Aᵀλ ≥ 1`, and on the value `bᵀλ`, without
floating point anywhere.
-/
namespace P32

/-! ## Index arithmetic: `J` is an up-set -/

/-- Shao's (18) forces every pair of indices to sum above 5. -/
theorem pair_gt (a b c : ℕ) (h : 5 * (a + b + c) < a * b + b * c + c * a) : 5 < b + c := by
  by_contra hbc
  push Not at hbc
  have hb : b ≤ 5 := by omega
  have hc : c ≤ 5 := by omega
  nlinarith

/-- `J` is an up-set in every coordinate at once. This simultaneity lets Case A
feed `lemma_2_3` a set strictly larger than the index it came from. -/
theorem upset3 (a b c a' b' c' : ℕ) (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (h : 5 * (a + b + c) < a * b + b * c + c * a) :
    5 * (a' + b' + c') < a' * b' + b' * c' + c' * a' := by
  have h1 : 5 < b + c := pair_gt a b c h
  have h2 : 5 < a + c := pair_gt b a c (by linarith)
  have h3 : 5 < a + b := pair_gt c a b (by linarith)
  nlinarith

/-- The real-valued pair lemma, for the step from (16) to (17). -/
theorem pair_real (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : 5 * (a + b + c) < a * b + b * c + c * a) : 5 < b + c := by
  by_contra hbc
  push Not at hbc
  have hb5 : b ≤ 5 := by linarith
  have hc5 : c ≤ 5 := by linarith
  nlinarith

/-- Shao's "since `nᵢ ≥ Fᵢ`, we have by (16), (17)", which the paper asserts
without proof, and which holds because raising each coordinate keeps
`T > 0`. -/
theorem mono17 (a b c A B C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C)
    (h : 5 * (a + b + c) < a * b + b * c + c * a) :
    5 * (A + B + C) < A * B + B * C + C * A := by
  have h1 : 5 < b + c := pair_real a b c ha hb hc h
  have h2 : 5 < a + c := pair_real b a c hb ha hc (by linarith)
  have h3 : 5 < a + b := pair_real c a b hc ha hb (by linarith)
  nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

theorem sum_le_card (g : ℕ → ℝ) (hi : ∀ k, g k ≤ 1) (n : ℕ) :
    (∑ k ∈ range n, g k) ≤ (n : ℝ) := by
  calc (∑ k ∈ range n, g k) ≤ ∑ _k ∈ range n, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => hi k)
    _ = (n : ℝ) := by simp

/-! ## Moving off `Fin n`

Every later step is `Finset.range` arithmetic, so the sorted tuple is extended
to `ℕ → ℝ` by zero at once and stays there. -/

/-- Extend a `Fin N` tuple to `ℕ` by zero. -/
noncomputable def ext {N : ℕ} (a : Fin N → ℝ) : ℕ → ℝ :=
  fun k => if h : k < N then a ⟨k, h⟩ else 0

theorem ext_lt {N : ℕ} (a : Fin N → ℝ) {k : ℕ} (h : k < N) : ext a k = a ⟨k, h⟩ := dif_pos h

theorem ext_ge {N : ℕ} (a : Fin N → ℝ) {k : ℕ} (h : ¬ k < N) : ext a k = 0 := dif_neg h

theorem sum_ext {N : ℕ} (a : Fin N → ℝ) : (∑ k ∈ range N, ext a k) = ∑ i, a i := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => by rw [ext_lt a i.2])

/-- Everything Proposition 3.2 needs about one `fᵢ`, gathered into one package,
namely its support `A` inside `U 15`, the decreasing rearrangement `g` of its
values
extended by zero, the fact that `g` reproduces the unit-sum of `f`, and the
clause that hands Case A a subset of `A` of size at least `k+1` on which
`f ≥ g k`. -/
theorem package (f : ZMod 15 → ℝ) (h0 : ∀ z, 0 ≤ f z) (h1 : ∀ z, f z ≤ 1) :
    ∃ (A : Finset (ZMod 15)) (g : ℕ → ℝ),
      A ⊆ Statements.U 15 ∧
      (∀ z ∈ A, 0 < f z) ∧
      (∀ k, 0 ≤ g k) ∧ (∀ k, g k ≤ 1) ∧
      (∑ k ∈ range A.card, g k) = (∑ z ∈ Statements.U 15, f z) ∧
      (∀ k, k < A.card → ∃ B : Finset (ZMod 15), B ⊆ A ∧ k + 1 ≤ B.card ∧
        ∀ z ∈ B, g k ≤ f z) := by
  classical
  set A : Finset (ZMod 15) := (Statements.U 15).filter (fun z => 0 < f z) with hAdef
  obtain ⟨a, hanti, hval, hsum, hcnt⟩ := exists_antitone_rearrangement A f
  refine ⟨A, ext a, Finset.filter_subset _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; exact (Finset.mem_filter.mp hz).2
  · intro k
    by_cases hk : k < A.card
    · rw [ext_lt a hk]
      obtain ⟨z, _, hzv⟩ := hval ⟨k, hk⟩
      rw [← hzv]; exact h0 z
    · rw [ext_ge a hk]
  · intro k
    by_cases hk : k < A.card
    · rw [ext_lt a hk]
      obtain ⟨z, _, hzv⟩ := hval ⟨k, hk⟩
      rw [← hzv]; exact h1 z
    · rw [ext_ge a hk]; norm_num
  · rw [sum_ext a, hsum]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hz hz'
    simp only [Finset.mem_filter, not_and, not_lt] at hz'
    exact le_antisymm (hz' hz) (h0 z)
  · intro k hk
    refine ⟨A.filter (fun z => ext a k ≤ f z), Finset.filter_subset _ _, ?_, ?_⟩
    · have := hcnt ⟨k, hk⟩
      rw [ext_lt a hk]
      exact this
    · intro z hz; exact (Finset.mem_filter.mp hz).2

/-! ## The four endgame quadratic facts.

Write `T x y z = x*y + y*z + z*x - 5*(x+y+z)`. Each of the four says `T ≤ 0`
under a bound on the total `x+y+z`, and that contradicts the strict `T > 0` of
Shao's hypothesis (16). -/

theorem E4 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hS : a + b + c ≤ 15) : a * b + b * c + c * a ≤ 5 * (a + b + c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a + b + c)]

theorem E1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ 2) (hS : a + b + c ≤ 16) : a * b + b * c + c * a ≤ 5 * (a + b + c) := by
  nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - 14), mul_nonneg hb hc,
    mul_nonneg ha (add_nonneg hb hc)]

theorem E2 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ 3) (hS : a + b + c ≤ 31 / 2) : a * b + b * c + c * a ≤ 5 * (a + b + c) := by
  nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - 25 / 2), mul_nonneg hb hc,
    mul_nonneg ha (add_nonneg hb hc)]

theorem E3 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a + b ≤ 8) (hS : a + b + c ≤ 31 / 2) : a * b + b * c + c * a ≤ 5 * (a + b + c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 8), mul_nonneg ha hb,
    mul_nonneg hc (add_nonneg ha hb)]

/-! ## The constraint family (19), and the 36 linear programs. -/

/-- Shao's constraint family (19), in 0-based indices, saying that for every
index triple in `J` the three selected values add to at most `3/2`. -/
def Con (g₁ g₂ g₃ : ℕ → ℝ) (n₁ n₂ n₃ : ℕ) : Prop :=
  ∀ k₁ k₂ k₃ : ℕ, k₁ < n₁ → k₂ < n₂ → k₃ < n₃ →
    5 * ((k₁ + 1) + (k₂ + 1) + (k₃ + 1))
        < (k₁ + 1) * (k₂ + 1) + (k₂ + 1) * (k₃ + 1) + (k₃ + 1) * (k₁ + 1) →
    g₁ k₁ + g₂ k₂ + g₃ k₃ ≤ 3 / 2

theorem lp_2_7_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 2 7 8)
    : (∑ k ∈ range 2, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 16 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 4,
    hi₂ 5,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5,
    hi₃ 6]

theorem lp_2_8_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 2 8 8)
    : (∑ k ∈ range 2, g₁ k) + (∑ k ∈ range 8, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 16 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 1 7 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    lo₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 4,
    hi₂ 5,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5]

theorem lp_3_6_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 3 6 7)
    : (∑ k ∈ range 3, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 4,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5]

theorem lp_3_6_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 3 6 8)
    : (∑ k ∈ range 3, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 31/2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 4,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5,
    hi₃ 7]

theorem lp_3_7_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 3 7 7)
    : (∑ k ∈ range 3, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    lo₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 4,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_3_7_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 3 7 8)
    : (∑ k ∈ range 3, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 4,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5]

theorem lp_3_8_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 3 8 8)
    : (∑ k ∈ range 3, g₁ k) + (∑ k ∈ range 8, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 31/2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 1 7 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    lo₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 4,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_4_5_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 5 7)
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 5, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5]

theorem lp_4_5_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 5 8)
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 5, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 31/2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5,
    hi₃ 7]

theorem lp_4_6_6 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 6 6)
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 6, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 4,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_4_6_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 6 7)
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    lo₁ 3,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_4_6_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 6 8)
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5]

theorem lp_4_7_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 7 7)
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 5,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_4_7_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 7 8)
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    lo₁ 3,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_4_8_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 8 8)
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 8, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 31/2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 1 7 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₂ 5,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_5_5_6 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 5 6)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 5, g₂ k) + (∑ k ∈ range 6, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₁ 3,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_5_5_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 5 7)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 5, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₁ 3,
    lo₁ 4,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_5_5_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 5 8)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 5, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5]

theorem lp_5_6_6 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 6 6)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 6, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₁ 3,
    lo₁ 4,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3]

theorem lp_5_6_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 6 7)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 4,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_5_6_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 6 8)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    lo₁ 4,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4]

theorem lp_5_7_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 7 7)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3]

theorem lp_5_7_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 7 8)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    lo₁ 4,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3]

theorem lp_5_8_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 5 8 8)
    : (∑ k ∈ range 5, g₁ k) + (∑ k ∈ range 8, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 1 7 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3]

theorem lp_6_6_6 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 6 6 6)
    : (∑ k ∈ range 6, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 6, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₁ 3,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 4,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3]

theorem lp_6_6_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 6 6 7)
    : (∑ k ∈ range 6, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3]

theorem lp_6_6_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 6 6 8)
    : (∑ k ∈ range 6, g₁ k) + (∑ k ∈ range 6, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    lo₁ 5,
    hi₂ 0,
    hi₂ 1,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3]

theorem lp_6_7_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 6 7 7)
    : (∑ k ∈ range 6, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 6 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    lo₁ 4,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2]

theorem lp_6_7_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 6 7 8)
    : (∑ k ∈ range 6, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3]

theorem lp_6_8_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 6 8 8)
    : (∑ k ∈ range 6, g₁ k) + (∑ k ∈ range 8, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 1 7 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 7 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 6 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    lo₁ 5,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2]

theorem lp_7_7_7 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 7 7 7)
    : (∑ k ∈ range 7, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 7, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 6 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 3]

theorem lp_7_7_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 7 7 8)
    : (∑ k ∈ range 7, g₁ k) + (∑ k ∈ range 7, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 3 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 6 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 6 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    lo₁ 4,
    hi₂ 0,
    hi₂ 1,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2]

theorem lp_7_8_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 7 8 8)
    : (∑ k ∈ range 7, g₁ k) + (∑ k ∈ range 8, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 6 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 6 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    lo₁ 6,
    hi₂ 0,
    hi₂ 1,
    hi₃ 0,
    hi₃ 1]

theorem lp_8_8_8 (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 8 8 8)
    : (∑ k ∈ range 8, g₁ k) + (∑ k ∈ range 8, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 4 7 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 5 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 6 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 7 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₃ 0,
    hi₃ 1]

theorem lp_4_5_8x (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 5 8)
    (hx : 8 ≤ (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 5, g₂ k))
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 5, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hx
  linarith [hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₁ 2,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hi₃ 4,
    hi₃ 5,
    hx]

theorem lp_4_8_8x (g₁ g₂ g₃ : ℕ → ℝ)
    (_lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (_lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (_lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ 4 8 8)
    (hx : 3 ≤ (∑ k ∈ range 4, g₁ k))
    : (∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 8, g₂ k) + (∑ k ∈ range 8, g₃ k) ≤ 15 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hx
  linarith [hc 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 2 7 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hc 3 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hi₁ 0,
    hi₁ 1,
    hi₂ 0,
    hi₂ 1,
    hi₂ 2,
    hi₂ 3,
    hi₃ 0,
    hi₃ 1,
    hi₃ 2,
    hi₃ 3,
    hx]

set_option maxHeartbeats 1000000 in
-- The 34 admissible sorted support-size triples: `interval_cases` walks the
-- 729 sorted boxes and `omega` kills the 695 that fail Shao's (17).
theorem cases34 (n₁ n₂ n₃ : ℕ) (h12 : n₁ ≤ n₂) (h23 : n₂ ≤ n₃) (h8 : n₃ ≤ 8)
    (hT : 5 * (n₁ + n₂ + n₃) < n₁ * n₂ + n₂ * n₃ + n₃ * n₁) :
    (n₁ = 2 ∧ n₂ = 7 ∧ n₃ = 8) ∨
    (n₁ = 2 ∧ n₂ = 8 ∧ n₃ = 8) ∨
    (n₁ = 3 ∧ n₂ = 6 ∧ n₃ = 7) ∨
    (n₁ = 3 ∧ n₂ = 6 ∧ n₃ = 8) ∨
    (n₁ = 3 ∧ n₂ = 7 ∧ n₃ = 7) ∨
    (n₁ = 3 ∧ n₂ = 7 ∧ n₃ = 8) ∨
    (n₁ = 3 ∧ n₂ = 8 ∧ n₃ = 8) ∨
    (n₁ = 4 ∧ n₂ = 5 ∧ n₃ = 7) ∨
    (n₁ = 4 ∧ n₂ = 5 ∧ n₃ = 8) ∨
    (n₁ = 4 ∧ n₂ = 6 ∧ n₃ = 6) ∨
    (n₁ = 4 ∧ n₂ = 6 ∧ n₃ = 7) ∨
    (n₁ = 4 ∧ n₂ = 6 ∧ n₃ = 8) ∨
    (n₁ = 4 ∧ n₂ = 7 ∧ n₃ = 7) ∨
    (n₁ = 4 ∧ n₂ = 7 ∧ n₃ = 8) ∨
    (n₁ = 4 ∧ n₂ = 8 ∧ n₃ = 8) ∨
    (n₁ = 5 ∧ n₂ = 5 ∧ n₃ = 6) ∨
    (n₁ = 5 ∧ n₂ = 5 ∧ n₃ = 7) ∨
    (n₁ = 5 ∧ n₂ = 5 ∧ n₃ = 8) ∨
    (n₁ = 5 ∧ n₂ = 6 ∧ n₃ = 6) ∨
    (n₁ = 5 ∧ n₂ = 6 ∧ n₃ = 7) ∨
    (n₁ = 5 ∧ n₂ = 6 ∧ n₃ = 8) ∨
    (n₁ = 5 ∧ n₂ = 7 ∧ n₃ = 7) ∨
    (n₁ = 5 ∧ n₂ = 7 ∧ n₃ = 8) ∨
    (n₁ = 5 ∧ n₂ = 8 ∧ n₃ = 8) ∨
    (n₁ = 6 ∧ n₂ = 6 ∧ n₃ = 6) ∨
    (n₁ = 6 ∧ n₂ = 6 ∧ n₃ = 7) ∨
    (n₁ = 6 ∧ n₂ = 6 ∧ n₃ = 8) ∨
    (n₁ = 6 ∧ n₂ = 7 ∧ n₃ = 7) ∨
    (n₁ = 6 ∧ n₂ = 7 ∧ n₃ = 8) ∨
    (n₁ = 6 ∧ n₂ = 8 ∧ n₃ = 8) ∨
    (n₁ = 7 ∧ n₂ = 7 ∧ n₃ = 7) ∨
    (n₁ = 7 ∧ n₂ = 7 ∧ n₃ = 8) ∨
    (n₁ = 7 ∧ n₂ = 8 ∧ n₃ = 8) ∨
    (n₁ = 8 ∧ n₂ = 8 ∧ n₃ = 8) := by
  interval_cases n₃ <;> interval_cases n₂ <;> interval_cases n₁ <;>
    first
      | (exfalso; omega)
      | simp

theorem caseB_sorted (n₁ n₂ n₃ : ℕ) (h12 : n₁ ≤ n₂) (h23 : n₂ ≤ n₃) (h8 : n₃ ≤ 8)
    (hT : 5 * (n₁ + n₂ + n₃) < n₁ * n₂ + n₂ * n₃ + n₃ * n₁)
    (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ n₁ n₂ n₃) :
    (∑ k ∈ range n₁, g₁ k) * (∑ k ∈ range n₂, g₂ k)
      + (∑ k ∈ range n₂, g₂ k) * (∑ k ∈ range n₃, g₃ k)
      + (∑ k ∈ range n₃, g₃ k) * (∑ k ∈ range n₁, g₁ k)
      ≤ 5 * ((∑ k ∈ range n₁, g₁ k) + (∑ k ∈ range n₂, g₂ k) + (∑ k ∈ range n₃, g₃ k)) := by
  have nn₁ : ∀ n : ℕ, 0 ≤ ∑ k ∈ range n, g₁ k :=
    fun n => Finset.sum_nonneg (fun k _ => lo₁ k)
  have nn₂ : ∀ n : ℕ, 0 ≤ ∑ k ∈ range n, g₂ k :=
    fun n => Finset.sum_nonneg (fun k _ => lo₂ k)
  have nn₃ : ∀ n : ℕ, 0 ≤ ∑ k ∈ range n, g₃ k :=
    fun n => Finset.sum_nonneg (fun k _ => lo₃ k)
  rcases cases34 n₁ n₂ n₃ h12 h23 h8 hT with
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · -- n = (2, 7, 8)
    refine E1 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) ?_ (lp_2_7_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
    have h := sum_le_card g₁ hi₁ 2
    push_cast at h; linarith
  · -- n = (2, 8, 8)
    refine E1 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) ?_ (lp_2_8_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
    have h := sum_le_card g₁ hi₁ 2
    push_cast at h; linarith
  · -- n = (3, 6, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_3_6_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (3, 6, 8)
    refine E2 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) ?_ (lp_3_6_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
    have h := sum_le_card g₁ hi₁ 3
    push_cast at h; linarith
  · -- n = (3, 7, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_3_7_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (3, 7, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_3_7_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (3, 8, 8)
    refine E2 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) ?_ (lp_3_8_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
    have h := sum_le_card g₁ hi₁ 3
    push_cast at h; linarith
  · -- n = (4, 5, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_4_5_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (4, 5, 8)
    rcases le_total ((∑ k ∈ range 4, g₁ k) + (∑ k ∈ range 5, g₂ k)) 8 with hb | hb
    · exact E3 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) hb (lp_4_5_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
    · exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_4_5_8x g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc hb)
  · -- n = (4, 6, 6)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_4_6_6 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (4, 6, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_4_6_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (4, 6, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_4_6_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (4, 7, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_4_7_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (4, 7, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_4_7_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (4, 8, 8)
    rcases le_total (∑ k ∈ range 4, g₁ k) 3 with hb | hb
    · exact E2 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) hb (lp_4_8_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
    · exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_4_8_8x g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc hb)
  · -- n = (5, 5, 6)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_5_6 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (5, 5, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_5_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (5, 5, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_5_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (5, 6, 6)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_6_6 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (5, 6, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_6_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (5, 6, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_6_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (5, 7, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_7_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (5, 7, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_7_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (5, 8, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_5_8_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (6, 6, 6)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_6_6_6 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (6, 6, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_6_6_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (6, 6, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_6_6_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (6, 7, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_6_7_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (6, 7, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_6_7_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (6, 8, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_6_8_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (7, 7, 7)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_7_7_7 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (7, 7, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_7_7_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (7, 8, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_7_8_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)
  · -- n = (8, 8, 8)
    exact E4 _ _ _ (nn₁ _) (nn₂ _) (nn₃ _) (lp_8_8_8 g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc)

theorem caseB (n₁ n₂ n₃ : ℕ) (b₁ : n₁ ≤ 8) (b₂ : n₂ ≤ 8) (b₃ : n₃ ≤ 8)
    (hT : 5 * (n₁ + n₂ + n₃) < n₁ * n₂ + n₂ * n₃ + n₃ * n₁)
    (g₁ g₂ g₃ : ℕ → ℝ)
    (lo₁ : ∀ k, 0 ≤ g₁ k) (hi₁ : ∀ k, g₁ k ≤ 1)
    (lo₂ : ∀ k, 0 ≤ g₂ k) (hi₂ : ∀ k, g₂ k ≤ 1)
    (lo₃ : ∀ k, 0 ≤ g₃ k) (hi₃ : ∀ k, g₃ k ≤ 1)
    (hc : Con g₁ g₂ g₃ n₁ n₂ n₃) :
    (∑ k ∈ range n₁, g₁ k) * (∑ k ∈ range n₂, g₂ k)
      + (∑ k ∈ range n₂, g₂ k) * (∑ k ∈ range n₃, g₃ k)
      + (∑ k ∈ range n₃, g₃ k) * (∑ k ∈ range n₁, g₁ k)
      ≤ 5 * ((∑ k ∈ range n₁, g₁ k) + (∑ k ∈ range n₂, g₂ k) + (∑ k ∈ range n₃, g₃ k)) := by
  rcases le_total n₁ n₂ with p | p <;> rcases le_total n₂ n₃ with q | q <;>
    rcases le_total n₁ n₃ with r | r
  · -- order (1, 2, 3)
    have key := caseB_sorted n₁ n₂ n₃ (by omega) (by omega) (by omega) (by linarith)
      g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc
    linarith [key]
  · -- order (1, 2, 3)
    have key := caseB_sorted n₁ n₂ n₃ (by omega) (by omega) (by omega) (by linarith)
      g₁ g₂ g₃ lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hc
    linarith [key]
  · -- order (1, 3, 2)
    have hc' : Con g₁ g₃ g₂ n₁ n₃ n₂ := by
      intro j₁ j₂ j₃ a₁ a₂ a₃ d
      have h := hc j₁ j₃ j₂ a₁ a₃ a₂ (by linarith)
      linarith
    have key := caseB_sorted n₁ n₃ n₂ (by omega) (by omega) (by omega) (by linarith)
      g₁ g₃ g₂ lo₁ hi₁ lo₃ hi₃ lo₂ hi₂ hc'
    linarith [key]
  · -- order (3, 1, 2)
    have hc' : Con g₃ g₁ g₂ n₃ n₁ n₂ := by
      intro j₁ j₂ j₃ a₁ a₂ a₃ d
      have h := hc j₂ j₃ j₁ a₂ a₃ a₁ (by linarith)
      linarith
    have key := caseB_sorted n₃ n₁ n₂ (by omega) (by omega) (by omega) (by linarith)
      g₃ g₁ g₂ lo₃ hi₃ lo₁ hi₁ lo₂ hi₂ hc'
    linarith [key]
  · -- order (2, 1, 3)
    have hc' : Con g₂ g₁ g₃ n₂ n₁ n₃ := by
      intro j₁ j₂ j₃ a₁ a₂ a₃ d
      have h := hc j₂ j₁ j₃ a₂ a₁ a₃ (by linarith)
      linarith
    have key := caseB_sorted n₂ n₁ n₃ (by omega) (by omega) (by omega) (by linarith)
      g₂ g₁ g₃ lo₂ hi₂ lo₁ hi₁ lo₃ hi₃ hc'
    linarith [key]
  · -- order (2, 3, 1)
    have hc' : Con g₂ g₃ g₁ n₂ n₃ n₁ := by
      intro j₁ j₂ j₃ a₁ a₂ a₃ d
      have h := hc j₃ j₁ j₂ a₃ a₁ a₂ (by linarith)
      linarith
    have key := caseB_sorted n₂ n₃ n₁ (by omega) (by omega) (by omega) (by linarith)
      g₂ g₃ g₁ lo₂ hi₂ lo₃ hi₃ lo₁ hi₁ hc'
    linarith [key]
  · -- order (3, 2, 1)
    have hc' : Con g₃ g₂ g₁ n₃ n₂ n₁ := by
      intro j₁ j₂ j₃ a₁ a₂ a₃ d
      have h := hc j₃ j₂ j₁ a₃ a₂ a₁ (by linarith)
      linarith
    have key := caseB_sorted n₃ n₂ n₁ (by omega) (by omega) (by omega) (by linarith)
      g₃ g₂ g₁ lo₃ hi₃ lo₂ hi₂ lo₁ hi₁ hc'
    linarith [key]
  · -- order (3, 2, 1)
    have hc' : Con g₃ g₂ g₁ n₃ n₂ n₁ := by
      intro j₁ j₂ j₃ a₁ a₂ a₃ d
      have h := hc j₃ j₂ j₁ a₃ a₂ a₁ (by linarith)
      linarith
    have key := caseB_sorted n₃ n₂ n₁ (by omega) (by omega) (by omega) (by linarith)
      g₃ g₂ g₁ lo₃ hi₃ lo₂ hi₂ lo₁ hi₁ hc'
    linarith [key]

end P32

section Prop32

open P32

/-! ## Proposition 3.2 -/

private theorem cardU15 : (Statements.U 15).card = 8 := by
  rw [card_U]; decide

/-- Shao's Proposition 3.2, the weighted case `m = 15`.

Three functions `ZMod 15 → [0,1]` whose unit-sums `F₁, F₂, F₃` satisfy
`F₁F₂ + F₂F₃ + F₃F₁ > 5(F₁+F₂+F₃)` represent every `x : ZMod 15` as a sum of
three units with a positive product and a value sum above `3/2`. -/
theorem prop_3_2 : Statements.Prop32 := by
  intro f₁ f₂ f₃ hnn hle F₁ F₂ F₃ hF₁ hF₂ hF₃ hT x
  obtain ⟨A₁, g₁, hs₁, hp₁, lo₁, hi₁, hsum₁, hbr₁⟩ :=
    package f₁ (fun z => (hnn z).1) (fun z => (hle z).1)
  obtain ⟨A₂, g₂, hs₂, hp₂, lo₂, hi₂, hsum₂, hbr₂⟩ :=
    package f₂ (fun z => (hnn z).2.1) (fun z => (hle z).2.1)
  obtain ⟨A₃, g₃, hs₃, hp₃, lo₃, hi₃, hsum₃, hbr₃⟩ :=
    package f₃ (fun z => (hnn z).2.2) (fun z => (hle z).2.2)
  -- the support sizes are at most `phi 15 = 8`
  have b₁ : A₁.card ≤ 8 := cardU15 ▸ Finset.card_le_card hs₁
  have b₂ : A₂.card ≤ 8 := cardU15 ▸ Finset.card_le_card hs₂
  have b₃ : A₃.card ≤ 8 := cardU15 ▸ Finset.card_le_card hs₃
  have n₁ : 0 ≤ F₁ := hF₁ ▸ Finset.sum_nonneg (fun z _ => (hnn z).1)
  have n₂ : 0 ≤ F₂ := hF₂ ▸ Finset.sum_nonneg (fun z _ => (hnn z).2.1)
  have n₃ : 0 ≤ F₃ := hF₃ ▸ Finset.sum_nonneg (fun z _ => (hnn z).2.2)
  have c₁ : F₁ ≤ (A₁.card : ℝ) := by rw [hF₁, ← hsum₁]; exact sum_le_card g₁ hi₁ _
  have c₂ : F₂ ≤ (A₂.card : ℝ) := by rw [hF₂, ← hsum₂]; exact sum_le_card g₂ hi₂ _
  have c₃ : F₃ ≤ (A₃.card : ℝ) := by rw [hF₃, ← hsum₃]; exact sum_le_card g₃ hi₃ _
  -- Shao's (16) on the `F`s upgrades to (17) on the support sizes
  have hTn : 5 * (A₁.card + A₂.card + A₃.card)
      < A₁.card * A₂.card + A₂.card * A₃.card + A₃.card * A₁.card := by
    have := mono17 F₁ F₂ F₃ _ _ _ n₁ n₂ n₃ c₁ c₂ c₃ hT
    exact_mod_cast this
  by_cases hA : ∃ k₁ k₂ k₃ : ℕ, k₁ < A₁.card ∧ k₂ < A₂.card ∧ k₃ < A₃.card ∧
      (5 * ((k₁ + 1) + (k₂ + 1) + (k₃ + 1))
        < (k₁ + 1) * (k₂ + 1) + (k₂ + 1) * (k₃ + 1) + (k₃ + 1) * (k₁ + 1)) ∧
      3 / 2 < g₁ k₁ + g₂ k₂ + g₃ k₃
  · -- Case A: `lemma_2_3` on the three level sets
    obtain ⟨k₁, k₂, k₃, hk₁, hk₂, hk₃, hTk, hbig⟩ := hA
    obtain ⟨B₁, hB₁s, hB₁c, hB₁v⟩ := hbr₁ k₁ hk₁
    obtain ⟨B₂, hB₂s, hB₂c, hB₂v⟩ := hbr₂ k₂ hk₂
    obtain ⟨B₃, hB₃s, hB₃c, hB₃v⟩ := hbr₃ k₃ hk₃
    have hTB : 5 * (B₁.card + B₂.card + B₃.card)
        < B₁.card * B₂.card + B₂.card * B₃.card + B₃.card * B₁.card :=
      upset3 _ _ _ _ _ _ hB₁c hB₂c hB₃c hTk
    obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hxsum⟩ :=
      lemma_2_3 B₁ B₂ B₃ (hB₁s.trans hs₁) (hB₂s.trans hs₂) (hB₃s.trans hs₃) hTB x
    refine ⟨a₁, hs₁ (hB₁s ha₁), a₂, hs₂ (hB₂s ha₂), a₃, hs₃ (hB₃s ha₃), hxsum, ?_, ?_⟩
    · exact mul_pos (mul_pos (hp₁ _ (hB₁s ha₁)) (hp₂ _ (hB₂s ha₂))) (hp₃ _ (hB₃s ha₃))
    · have v₁ := hB₁v a₁ ha₁
      have v₂ := hB₂v a₂ ha₂
      have v₃ := hB₃v a₃ ha₃
      linarith
  · -- Case B: Shao's (19) holds everywhere, and contradicts (16)
    exfalso
    push Not at hA
    have key := caseB A₁.card A₂.card A₃.card b₁ b₂ b₃ hTn g₁ g₂ g₃
      lo₁ hi₁ lo₂ hi₂ lo₃ hi₃ hA
    rw [hsum₁, hsum₂, hsum₃, ← hF₁, ← hF₂, ← hF₃] at key
    linarith

/-! ### Anti-vacuity for `prop_3_2`

Two witnesses are needed here, because the first of them establishes less than
its statement suggests and the second supplies what it misses.
-/

/-- The hypothesis class is inhabited, as the constant `7/10` shows, since each
`Fᵢ` is then `8 * 7/10 = 28/5` and `5(F₁+F₂+F₃) = 84 < 2352/25 = F₁F₂+F₂F₃+F₃F₁`,
so the hypothesis holds strictly. What this witness does not establish is the
value clause, which degenerates at a constant `f` into the arithmetic statement
`3/2 < 21/10`, true of any triple whatever, so satisfiability of the hypothesis
is all that it certifies. -/
example : (5 : ℝ) * (28 / 5 + 28 / 5 + 28 / 5)
    < 28 / 5 * (28 / 5) + 28 / 5 * (28 / 5) + 28 / 5 * (28 / 5) := by norm_num

/-- The conclusion costs something too, as the following two-valued `f` on the
units mod 15 shows. Let `f` equal `1` on `{1,2,4,7,8}` and `1/4` on the other
three, so that each `Fᵢ` is `5 + 3/4 = 23/4` and the hypothesis holds. The value
clause now matters, since three values drawn from `{1, 1/4}` exceed `3/2`
only when at least two of them are `1`, so the triple the theorem returns cannot
be an arbitrary representation of `0`, and exhibiting some triple of units
summing to `0` would not prove the statement below. -/
example : ∃ a₁ ∈ Statements.U 15, ∃ a₂ ∈ Statements.U 15, ∃ a₃ ∈ Statements.U 15,
    a₁ + a₂ + a₃ = (0 : ZMod 15) ∧
    (3 : ℝ) / 2 < (fun z : ZMod 15 => if z = 1 ∨ z = 2 ∨ z = 4 ∨ z = 7 ∨ z = 8
        then (1 : ℝ) else 1 / 4) a₁
      + (fun z : ZMod 15 => if z = 1 ∨ z = 2 ∨ z = 4 ∨ z = 7 ∨ z = 8
        then (1 : ℝ) else 1 / 4) a₂
      + (fun z : ZMod 15 => if z = 1 ∨ z = 2 ∨ z = 4 ∨ z = 7 ∨ z = 8
        then (1 : ℝ) else 1 / 4) a₃ := by
  classical
  set f : ZMod 15 → ℝ :=
    fun z => if z = 1 ∨ z = 2 ∨ z = 4 ∨ z = 7 ∨ z = 8 then (1 : ℝ) else 1 / 4 with hf
  have h0 : ∀ z, 0 ≤ f z := by intro z; rw [hf]; dsimp only; split <;> norm_num
  have h1 : ∀ z, f z ≤ 1 := by intro z; rw [hf]; dsimp only; split <;> norm_num
  have hsum : (∑ z ∈ Statements.U 15, f z) = 23 / 4 := by
    rw [U15, hf]
    simp +decide
    norm_num
  obtain ⟨a₁, k₁, a₂, k₂, a₃, k₃, hx, -, hval⟩ :=
    prop_3_2 f f f (fun z => ⟨h0 z, h0 z, h0 z⟩) (fun z => ⟨h1 z, h1 z, h1 z⟩)
      (23 / 4) (23 / 4) (23 / 4) hsum.symm hsum.symm hsum.symm (by norm_num) 0
  exact ⟨a₁, k₁, a₂, k₂, a₃, k₃, hx, hval⟩

/-- The threshold is exactly where Shao puts it. At the constant `5/8`, where
each `Fᵢ = 5`, the hypothesis reads `75 < 75` and fails. -/
example : ¬ ((5 : ℝ) * (5 + 5 + 5) < 5 * 5 + 5 * 5 + 5 * 5) := by norm_num

end Prop32

/-! ## The CRT core of Proposition 1.4

The case `15 ∣ M` of Proposition 1.4 is everything the `WLOG` step above leaves.
Write `M = 15 * m'`, split `ZMod M` as `ZMod 15 × ZMod m'`, average `g` over the
`ZMod 15` fiber to get `f'` on `ZMod m'`, apply Proposition 3.1 to `f'`, and
then apply Proposition 3.2 to the three fiber functions.

The factor that makes the two propositions meet is `phi 15 = 8`. Proposition 3.1
returns the normalized inequality
`f'(a₁)f'(a₂) + f'(a₂)f'(a₃) + f'(a₃)f'(a₁) > 5/8 * (f'(a₁) + f'(a₂) + f'(a₃))`,
while Proposition 3.2 wants the unnormalized
`F₁F₂ + F₂F₃ + F₃F₁ > 5 * (F₁ + F₂ + F₃)` with `Fᵢ = 8 * f'(aᵢ)`, and
multiplying through by `64` matches the two exactly, with the `5` of
Proposition 3.2 appearing as `8 * (5/8)`.

The `WLOG` is discharged by destructing the divisibility, so `M` becomes the
literal `15 * m'` and `ZMod.chineseRemainder` applies on the nose.
-/

/-! ## Dictionary: membership in `U` and the CRT transport of a sum. -/

private theorem mem_U {m : ℕ} [NeZero m] {x : ZMod m} :
    x ∈ Statements.U m ↔ IsUnit x := by
  simp [Statements.U]

private theorem isUnit_crt {a b : ℕ} (h : Nat.Coprime a b) (x : ZMod (a * b)) :
    IsUnit x ↔ IsUnit ((ZMod.chineseRemainder h) x).1
        ∧ IsUnit ((ZMod.chineseRemainder h) x).2 := by
  rw [← Prod.isUnit_iff, isUnit_map_iff]

/-- The CRT equivalence carries `U (a*b)` onto `U a ×ˢ U b`, so any sum over the
units mod `a*b` is a sum over the product of the two unit sets. -/
private theorem sum_U_crt {a b : ℕ} [NeZero a] [NeZero b] [NeZero (a * b)]
    (h : Nat.Coprime a b) (g : ZMod (a * b) → ℝ) :
    ∑ x ∈ Statements.U (a * b), g x
      = ∑ p ∈ (Statements.U a) ×ˢ (Statements.U b),
          g ((ZMod.chineseRemainder h).symm p) := by
  classical
  refine Finset.sum_nbij' (fun x => (ZMod.chineseRemainder h) x)
    (fun p => (ZMod.chineseRemainder h).symm p) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_U] at hx
    rw [Finset.mem_product, mem_U, mem_U]
    exact (isUnit_crt h x).mp hx
  · intro p hp
    rw [Finset.mem_product, mem_U, mem_U] at hp
    rw [mem_U, isUnit_crt h]
    simpa using hp
  · intro x _; simp
  · intro p _; simp
  · intro x _; simp

/-- `sum_U_crt` phrased against a named copy `e` of the CRT equivalence, so the
main proof never has to unfold the abbreviation. -/
private theorem sum_U_crt' {a b : ℕ} [NeZero a] [NeZero b] [NeZero (a * b)]
    {h : Nat.Coprime a b} {e : ZMod (a * b) ≃+* ZMod a × ZMod b}
    (he : e = ZMod.chineseRemainder h) (g : ZMod (a * b) → ℝ) :
    ∑ x ∈ Statements.U (a * b), g x
      = ∑ p ∈ (Statements.U a) ×ˢ (Statements.U b), g (e.symm p) := by
  subst he; exact sum_U_crt h g

/-- A pair of units pulls back to a unit mod `a * b`. -/
private theorem mem_U_symm {a b : ℕ} [NeZero a] [NeZero b] [NeZero (a * b)]
    {h : Nat.Coprime a b} {e : ZMod (a * b) ≃+* ZMod a × ZMod b}
    (he : e = ZMod.chineseRemainder h) {p : ZMod a × ZMod b}
    (h1 : p.1 ∈ Statements.U a) (h2 : p.2 ∈ Statements.U b) :
    e.symm p ∈ Statements.U (a * b) := by
  subst he
  rw [mem_U] at h1 h2 ⊢
  rw [isUnit_crt h, RingEquiv.apply_symm_apply]
  exact ⟨h1, h2⟩

/-! ## Node `prop_3_1`: the induction away from 3 and 5

Shao's Proposition 3.1, arXiv:1206.6139v2, proved by strong induction on `m`
over the squarefree moduli coprime to `30`.

Both cases make the same three moves. Sort the values of the relevant function
on the units mod a prime `p` into an antitone tuple of length `p - 1`, run the
contrapositive of an averaging lemma to obtain one index triple `(i, j, k)` with
`i + j + k ≥ p - 1` on which the inequality runs strictly the other way, and
read three level sets off those indices. The counting clause of the
rearrangement gives `|I| + |J| + |K| ≥ (i+1) + (j+1) + (k+1) ≥ p + 2`, which is
the hypothesis `cd_chowla` asks for, and `p31_transfer` moves the strict
inequality up from the thresholds to the actual values; that common tail is
`p31_landing`.

The two cases differ in which averaging lemma runs, and on what.

* Base, `m = p` prime with `p ≥ 7`: `lemma_2_1` on the single sorted tuple of
  `f` on `U p`, at length `p - 1 ≥ 6`.
* Step, `m = m' * p` with `p` the largest prime factor: average `f` over the
  `ZMod p` fiber to get `f'` on `ZMod m'`, apply the induction hypothesis to
  `f'`, then run `lemma_2_2` on the three fiber sequences that the induction
  hypothesis picks out, at length `p - 1 ≥ 10`.

The largest prime factor is the right one to peel off, because a squarefree `m`
coprime to `30` has every prime factor at least `7`, and a composite one has at
least two of them, so its largest factor is at least `11` and the resulting
`p - 1 ≥ 10` clears the threshold of `lemma_2_2`. That argument is
`p31_factor`, and it is the only place where the choice of `p` matters.

The modulus `m = 1` is a separate one-line base case, since `ZMod 1` is trivial,
its only unit is `0`, and the density hypothesis is already the conclusion.
-/

/-- Helper for `p31_pairs_of_pos`, giving one of the three cyclic images. -/
private theorem p31m_pair_lb {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : 5 / 8 * (x + y + z) < x * y + y * z + z * x) :
    5 / 8 < y + z := by
  by_contra hcon
  have hc : y + z ≤ 5 / 8 := not_lt.mp hcon
  have hyz0 : (0:ℝ) ≤ y + z := by linarith
  have h1 : 0 ≤ x * (5 / 8 - (y + z)) := mul_nonneg hx (by linarith)
  have h2 : 0 ≤ (y + z) * (5 / 8 - (y + z)) := mul_nonneg hyz0 (by linarith)
  have h3 : 0 ≤ (y - z) ^ 2 := sq_nonneg (y - z)
  linarith [h1, h2, h3, h]

private theorem p31_pairs_of_pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : 5 / 8 * (x + y + z) < x * y + y * z + z * x) :
    5 / 8 < x + y ∧ 5 / 8 < y + z ∧ 5 / 8 < z + x := by
  refine ⟨?_, ?_, ?_⟩
  · have := p31m_pair_lb hz hx hy (by linarith)
    linarith
  · have := p31m_pair_lb hx hy hz (by linarith)
    linarith
  · have := p31m_pair_lb hy hz hx (by linarith)
    linarith

private theorem p31_transfer {x y z X Y Z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxX : x ≤ X) (hyY : y ≤ Y) (hzZ : z ≤ Z)
    (h : 5 / 8 * (x + y + z) < x * y + y * z + z * x) :
    5 / 8 * (X + Y + Z) < X * Y + Y * Z + Z * X := by
  obtain ⟨hxy, hyz, hzx⟩ := p31_pairs_of_pos hx hy hz h
  have s1 : 0 ≤ (X - x) * ((y + z) - 5 / 8) := mul_nonneg (by linarith) (by linarith)
  have s2 : 0 ≤ (Y - y) * ((X + z) - 5 / 8) := mul_nonneg (by linarith) (by linarith)
  have s3 : 0 ≤ (Z - z) * ((X + Y) - 5 / 8) := mul_nonneg (by linarith) (by linarith)
  linarith [s1, s2, s3, h]


/-- A prime dividing a number coprime to `30` is at least `7`. -/
private theorem pf_seven_le_of_prime_dvd {m p : ℕ} (hp : p.Prime) (hpd : p ∣ m)
    (hcop : Nat.Coprime m 30) : 7 ≤ p := by
  have hp30 : ¬ p ∣ 30 := by
    intro h
    have h1 : p ∣ Nat.gcd m 30 := Nat.dvd_gcd hpd h
    rw [hcop] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  rcases Nat.lt_or_ge p 7 with hlt | hge
  · have h2 : 2 ≤ p := hp.two_le
    interval_cases p <;> revert hp hp30 <;> decide
  · exact hge

private theorem p31_factor (m : ℕ) (hm0 : m ≠ 0) (hsq : Squarefree m)
    (hcop : Nat.Coprime m 30) (hm1 : m ≠ 1) :
    ∃ p m' : ℕ, p.Prime ∧ 7 ≤ p ∧ m = m' * p ∧ Nat.Coprime m' p ∧
      m' ≠ 0 ∧ Squarefree m' ∧ Nat.Coprime m' 30 ∧ m' < m ∧ (m' = 1 ∨ 11 ≤ p) := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hne : m.primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    omega
  obtain ⟨p, hpmem, hmax⟩ : ∃ p ∈ m.primeFactors, ∀ q ∈ m.primeFactors, q ≤ p :=
    ⟨m.primeFactors.max' hne, Finset.max'_mem _ hne, fun q hq => Finset.le_max' _ q hq⟩
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hpmem
  have h7 : 7 ≤ p := pf_seven_le_of_prime_dvd hp hpd hcop
  have hmeq : m = m / p * p := (Nat.div_mul_cancel hpd).symm
  have hdvd' : m / p ∣ m := Nat.div_dvd_of_dvd hpd
  have hnd : ¬ p ∣ m / p := by
    intro h
    obtain ⟨k, hk⟩ := h
    have hpp : p * p ∣ m := ⟨k, by rw [hmeq, hk]; ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p hpp))
  have hcopm : Nat.Coprime (m / p) p := (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hm'0 : m / p ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmeq
    exact hm0 hmeq
  refine ⟨p, m / p, hp, h7, hmeq, hcopm, hm'0,
    hsq.squarefree_of_dvd hdvd', Nat.Coprime.coprime_dvd_left hdvd' hcop,
    Nat.div_lt_self hmpos (by omega), ?_⟩
  by_cases hm' : m / p = 1
  · exact Or.inl hm'
  refine Or.inr ?_
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hm'
  have hqm : q ∣ m := hqd.trans hdvd'
  have hq7 : 7 ≤ q := pf_seven_le_of_prime_dvd hq hqm hcop
  have hqmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqm, hm0⟩
  have hqle : q ≤ p := hmax q hqmem
  have hqne : q ≠ p := by
    rintro rfl
    exact hnd hqd
  have h8 : 8 ≤ p := by omega
  rcases Nat.lt_or_ge p 11 with hc | hge
  · interval_cases p <;> revert hp <;> decide
  · exact hge

private theorem p31_landing {p : ℕ} [NeZero p] (hp : p.Prime)
    (f₁ f₂ f₃ : ZMod p → ℝ) (v₁ v₂ v₃ : ℝ)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hstrict : 5 / 8 * (v₁ + v₂ + v₃) < v₁ * v₂ + v₂ * v₃ + v₃ * v₁)
    (htrans : ∀ x y z X Y Z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → x ≤ X → y ≤ Y → z ≤ Z →
      5 / 8 * (x + y + z) < x * y + y * z + z * x → 5 / 8 * (X + Y + Z) < X * Y + Y * Z + Z * X)
    (c₁ c₂ c₃ : ℕ)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hc₃ : 1 ≤ c₃)
    (hs : p + 2 ≤ c₁ + c₂ + c₃)
    (hf₁ : c₁ ≤ ((Statements.U p).filter (fun t => v₁ ≤ f₁ t)).card)
    (hf₂ : c₂ ≤ ((Statements.U p).filter (fun t => v₂ ≤ f₂ t)).card)
    (hf₃ : c₃ ≤ ((Statements.U p).filter (fun t => v₃ ≤ f₃ t)).card)
    (x : ZMod p) :
    ∃ u ∈ Statements.U p, ∃ v ∈ Statements.U p, ∃ w ∈ Statements.U p,
      u + v + w = x ∧
      5 / 8 * (f₁ u + f₂ v + f₃ w) < f₁ u * f₂ v + f₂ v * f₃ w + f₃ w * f₁ u := by
  classical
  set I : Finset (ZMod p) := (Statements.U p).filter (fun t => v₁ ≤ f₁ t) with hI
  set J : Finset (ZMod p) := (Statements.U p).filter (fun t => v₂ ≤ f₂ t) with hJ
  set K : Finset (ZMod p) := (Statements.U p).filter (fun t => v₃ ≤ f₃ t) with hK
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : p + 2 ≤ I.card + J.card + K.card := by omega
  obtain ⟨u, hu, v, hv, w, hw, huvw⟩ :=
    cd_chowla p hp I J K hIne hJne hKne hcard x
  rw [hI, Finset.mem_filter] at hu
  rw [hJ, Finset.mem_filter] at hv
  rw [hK, Finset.mem_filter] at hw
  exact ⟨u, hu.1, v, hv.1, w, hw.1, huvw,
    htrans v₁ v₂ v₃ (f₁ u) (f₂ v) (f₃ w) hv₁ hv₂ hv₃ hu.2 hv.2 hw.2 hstrict⟩

/-! ## Node `prop_3_1` -/

/-- The contrapositive of `lemma_2_1`, in the form Proposition 3.1 consumes,
namely that an average above `5/8` yields a single index triple summing to at
least `n` on which the inequality runs strictly the other way. -/
private theorem l21_contra {n : ℕ} (hn : 6 ≤ n) (hev : Even n) (a : Fin n → ℝ)
    (hanti : Antitone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1)
    (hbig : 5 / 8 * (n : ℝ) < ∑ i, a i) :
    ∃ i j k : Fin n, n ≤ (i : ℕ) + (j : ℕ) + (k : ℕ) ∧
      5 / 8 * (a i + a j + a k) < a i * a j + a j * a k + a k * a i := by
  by_contra hcon
  push Not at hcon
  have := lemma_2_1 n hn hev a hanti h0 h1 (fun i j k h => hcon i j k h)
  linarith

/-- The contrapositive of `lemma_2_2`, the asymmetric version of `l21_contra`. -/
private theorem l22_contra {n : ℕ} (hn : 10 ≤ n) (hev : Even n) (a b c : Fin n → ℝ)
    (ha : Antitone a) (hb : Antitone b) (hc : Antitone c)
    (h0 : ∀ i, 0 ≤ a i ∧ 0 ≤ b i ∧ 0 ≤ c i) (h1 : ∀ i, a i ≤ 1 ∧ b i ≤ 1 ∧ c i ≤ 1)
    (A B C : ℝ) (hA : A = (∑ i, a i) / n) (hB : B = (∑ i, b i) / n)
    (hC : C = (∑ i, c i) / n)
    (hbig : 5 / 8 * (A + B + C) < A * B + B * C + C * A) :
    ∃ i j k : Fin n, n ≤ (i : ℕ) + (j : ℕ) + (k : ℕ) ∧
      5 / 8 * (a i + b j + c k) < a i * b j + b j * c k + c k * a i := by
  by_contra hcon
  push Not at hcon
  have := lemma_2_2 n hn hev a b c ha hb hc h0 h1
    (fun i j k h => hcon i j k h) A B C hA hB hC
  linarith

/-- `phi p = p - 1` at a prime, read off the unit `Finset`. -/
private theorem card_U_prime {p : ℕ} [NeZero p] (hp : p.Prime) :
    (Statements.U p).card = p - 1 := by
  rw [card_U, Nat.totient_prime hp]

/-- The unit count at an odd prime is even and at least `p - 1`, and those are
exactly the two properties the averaging lemmas need of the index length. -/
private theorem even_card_U_prime {p : ℕ} [NeZero p] (hp : p.Prime) (hp3 : 3 ≤ p) :
    Even (Statements.U p).card := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  exact ⟨k, by rw [card_U_prime hp]; omega⟩

/-- `exists_antitone_rearrangement` at `S = U p`, with the value bounds carried
through, so that the output is in the exact input shape of `l21_contra` and
`l22_contra`. -/
private theorem p31_sorted {p : ℕ} [NeZero p] (g : ZMod p → ℝ)
    (h0 : ∀ t, 0 ≤ g t) (h1 : ∀ t, g t ≤ 1) :
    ∃ α : Fin (Statements.U p).card → ℝ, Antitone α ∧ (∀ i, 0 ≤ α i) ∧
      (∀ i, α i ≤ 1) ∧ (∑ i, α i) = ∑ t ∈ Statements.U p, g t ∧
      (∀ i : Fin (Statements.U p).card, (i : ℕ) + 1
        ≤ ((Statements.U p).filter (fun t => α i ≤ g t)).card) := by
  obtain ⟨α, hanti, hval, hsum, hcount⟩ :=
    exists_antitone_rearrangement (Statements.U p) g
  refine ⟨α, hanti, ?_, ?_, hsum, hcount⟩
  · intro i; obtain ⟨t, -, ht⟩ := hval i; rw [← ht]; exact h0 t
  · intro i; obtain ⟨t, -, ht⟩ := hval i; rw [← ht]; exact h1 t

/-- The base case of Proposition 3.1, `m = p` prime with `p ≥ 7`. Sort the
values of `f` on the units, take the triple that `l21_contra` returns, and
land it with `p31_landing`. -/
private theorem p31_base {p : ℕ} [NeZero p] (hp : p.Prime) (hp7 : 7 ≤ p)
    (f : ZMod p → ℝ) (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1)
    (hdens : (5 : ℝ) / 8 * (Nat.totient p) < ∑ t ∈ Statements.U p, f t)
    (x : ZMod p) :
    ∃ a ∈ Statements.U p, ∃ b ∈ Statements.U p, ∃ c ∈ Statements.U p, a + b + c = x ∧
      5 / 8 * (f a + f b + f c) < f a * f b + f b * f c + f c * f a := by
  obtain ⟨α, hanti, hα0, hα1, hsum, hcount⟩ := p31_sorted f h0 h1
  have hcard : (Statements.U p).card = Nat.totient p := card_U p
  have hN : (Statements.U p).card = p - 1 := card_U_prime hp
  have hbig : 5 / 8 * (((Statements.U p).card : ℕ) : ℝ) < ∑ i, α i := by
    rw [hsum, hcard]; exact hdens
  obtain ⟨i, j, k, hijk, hstrict⟩ :=
    l21_contra (by omega) (even_card_U_prime hp (by omega)) α hanti hα0 hα1 hbig
  exact p31_landing hp f f f (α i) (α j) (α k) (hα0 i) (hα0 j) (hα0 k) hstrict
    (fun x y z X Y Z hx hy hz hxX hyY hzZ h => p31_transfer hx hy hz hxX hyY hzZ h)
    ((i : ℕ) + 1) ((j : ℕ) + 1) ((k : ℕ) + 1) (by omega) (by omega) (by omega)
    (by omega) (hcount i) (hcount j) (hcount k) x

/-- The induction step of Proposition 3.1, `m = m' * p` with `p` the largest
prime factor, so that `p ≥ 11` and the fiber length `p - 1` clears the threshold
of `10` that `lemma_2_2` imposes. Average `f` over the `ZMod p` fiber, feed the
average to the induction hypothesis on `m'`, then run `lemma_2_2` on the three
fiber sequences the induction hypothesis picks out. -/
private theorem p31_step {m' p : ℕ} [NeZero m'] [NeZero p] [NeZero (m' * p)]
    (hp : p.Prime) (hp11 : 11 ≤ p) (hcop : Nat.Coprime m' p)
    (IH : ∀ g : ZMod m' → ℝ, (∀ t, 0 ≤ g t) → (∀ t, g t ≤ 1) →
      (5 : ℝ) / 8 * (Nat.totient m') < (∑ t ∈ Statements.U m', g t) →
      ∀ s : ZMod m', ∃ a ∈ Statements.U m', ∃ b ∈ Statements.U m',
        ∃ c ∈ Statements.U m', a + b + c = s ∧
        5 / 8 * (g a + g b + g c) < g a * g b + g b * g c + g c * g a)
    (f : ZMod (m' * p) → ℝ) (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1)
    (hdens : (5 : ℝ) / 8 * (Nat.totient (m' * p)) < ∑ t ∈ Statements.U (m' * p), f t)
    (x : ZMod (m' * p)) :
    ∃ a ∈ Statements.U (m' * p), ∃ b ∈ Statements.U (m' * p),
      ∃ c ∈ Statements.U (m' * p), a + b + c = x ∧
      5 / 8 * (f a + f b + f c) < f a * f b + f b * f c + f c * f a := by
  obtain ⟨e, he⟩ : ∃ e : ZMod (m' * p) ≃+* ZMod m' × ZMod p,
      e = ZMod.chineseRemainder hcop := ⟨_, rfl⟩
  have hN : (Statements.U p).card = p - 1 := card_U_prime hp
  have hNtot : (((Statements.U p).card : ℕ) : ℝ) = (Nat.totient p : ℝ) := by
    rw [card_U]
  have hNpos : (0 : ℝ) < (((Statements.U p).card : ℕ) : ℝ) := by
    have : 0 < (Statements.U p).card := by omega
    exact_mod_cast this
  have hNne : (((Statements.U p).card : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  -- the fiber average on `ZMod m'`
  obtain ⟨f', hf'val⟩ : ∃ f' : ZMod m' → ℝ, ∀ s, f' s
      = (1 / (((Statements.U p).card : ℕ) : ℝ))
        * ∑ t ∈ Statements.U p, f (e.symm (s, t)) := ⟨_, fun _ => rfl⟩
  have hf'0 : ∀ s, 0 ≤ f' s := by
    intro s
    rw [hf'val s]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun t _ => h0 (e.symm (s, t))))
  have hcardN : (∑ _t ∈ Statements.U p, (1 : ℝ))
      = (((Statements.U p).card : ℕ) : ℝ) := by
    rw [Finset.sum_const]; simp
  have hf'1 : ∀ s, f' s ≤ 1 := by
    intro s
    have hle : ∑ t ∈ Statements.U p, f (e.symm (s, t))
        ≤ ∑ _t ∈ Statements.U p, (1 : ℝ) := Finset.sum_le_sum (fun t _ => h1 _)
    rw [hcardN] at hle
    have := mul_le_mul_of_nonneg_left hle
      (show (0 : ℝ) ≤ 1 / (((Statements.U p).card : ℕ) : ℝ) by positivity)
    rw [one_div, inv_mul_cancel₀ hNne] at this
    rw [hf'val s, one_div]
    exact this
  -- the density hypothesis transports through the CRT splitting
  have hsumsplit : ∑ s ∈ Statements.U m', (∑ t ∈ Statements.U p, f (e.symm (s, t)))
      = ∑ z ∈ Statements.U (m' * p), f z := by
    rw [sum_U_crt' he f, Finset.sum_product]
  have hsumf' : ∑ s ∈ Statements.U m', f' s
      = (1 / (((Statements.U p).card : ℕ) : ℝ))
        * ∑ z ∈ Statements.U (m' * p), f z := by
    rw [Finset.sum_congr rfl (fun s _ => hf'val s), ← hsumsplit, Finset.mul_sum]
  have htot : ((Nat.totient (m' * p) : ℕ) : ℝ)
      = (Nat.totient m' : ℝ) * (((Statements.U p).card : ℕ) : ℝ) := by
    rw [Nat.totient_mul hcop, Nat.cast_mul, hNtot]
  have hdens' : (5 : ℝ) / 8 * (Nat.totient m') < ∑ s ∈ Statements.U m', f' s := by
    rw [htot] at hdens
    rw [hsumf', one_div]
    have h := mul_lt_mul_of_pos_left hdens
      (show (0 : ℝ) < 1 / (((Statements.U p).card : ℕ) : ℝ) by positivity)
    rw [show (1 / (((Statements.U p).card : ℕ) : ℝ))
        * (5 / 8 * ((Nat.totient m' : ℝ) * (((Statements.U p).card : ℕ) : ℝ)))
        = 5 / 8 * (Nat.totient m' : ℝ)
          * ((1 / (((Statements.U p).card : ℕ) : ℝ))
            * (((Statements.U p).card : ℕ) : ℝ)) from by ring] at h
    rw [one_div, inv_mul_cancel₀ hNne, mul_one] at h
    exact h
  -- Proposition 3.1 at `m'`, by the induction hypothesis
  obtain ⟨a, ha, b, hb, c, hc, habc, hkey⟩ := IH f' hf'0 hf'1 hdens' (e x).1
  -- the three fiber sequences on `ZMod p`, sorted
  obtain ⟨α, hαanti, hα0, hα1, hαsum, hαc⟩ :=
    p31_sorted (p := p) (fun t => f (e.symm (a, t))) (fun t => h0 _) (fun t => h1 _)
  obtain ⟨β, hβanti, hβ0, hβ1, hβsum, hβc⟩ :=
    p31_sorted (p := p) (fun t => f (e.symm (b, t))) (fun t => h0 _) (fun t => h1 _)
  obtain ⟨γ, hγanti, hγ0, hγ1, hγsum, hγc⟩ :=
    p31_sorted (p := p) (fun t => f (e.symm (c, t))) (fun t => h0 _) (fun t => h1 _)
  have hAeq : f' a = (∑ i, α i) / (((Statements.U p).card : ℕ) : ℝ) := by
    rw [hf'val a, hαsum]; ring
  have hBeq : f' b = (∑ i, β i) / (((Statements.U p).card : ℕ) : ℝ) := by
    rw [hf'val b, hβsum]; ring
  have hCeq : f' c = (∑ i, γ i) / (((Statements.U p).card : ℕ) : ℝ) := by
    rw [hf'val c, hγsum]; ring
  obtain ⟨i, j, k, hijk, hstrict⟩ :=
    l22_contra (by omega) (even_card_U_prime hp (by omega)) α β γ
      hαanti hβanti hγanti (fun i => ⟨hα0 i, hβ0 i, hγ0 i⟩)
      (fun i => ⟨hα1 i, hβ1 i, hγ1 i⟩) (f' a) (f' b) (f' c) hAeq hBeq hCeq hkey
  obtain ⟨u, hu, v, hv, w, hw, huvw, hval⟩ :=
    p31_landing hp (fun t => f (e.symm (a, t))) (fun t => f (e.symm (b, t)))
      (fun t => f (e.symm (c, t))) (α i) (β j) (γ k) (hα0 i) (hβ0 j) (hγ0 k) hstrict
      (fun x y z X Y Z hx hy hz hxX hyY hzZ h => p31_transfer hx hy hz hxX hyY hzZ h)
      ((i : ℕ) + 1) ((j : ℕ) + 1) ((k : ℕ) + 1) (by omega) (by omega) (by omega)
      (by omega) (hαc i) (hβc j) (hγc k) (e x).2
  refine ⟨e.symm (a, u), mem_U_symm he ha hu, e.symm (b, v), mem_U_symm he hb hv,
    e.symm (c, w), mem_U_symm he hc hw, ?_, hval⟩
  have hadd : e.symm (a, u) + e.symm (b, v) + e.symm (c, w)
      = e.symm ((a, u) + (b, v) + (c, w)) := by simp only [map_add]
  rw [hadd]
  have hpair : ((a, u) + (b, v) + (c, w) : ZMod m' × ZMod p) = e x := by
    rw [Prod.ext_iff]
    exact ⟨by simpa using habc, by simpa using huvw⟩
  rw [hpair, RingEquiv.symm_apply_apply]

/-- The remaining base case `m = 1`. Since `ZMod 1` is trivial its only unit is
`0`, so the density hypothesis reads `f 0 > 5/8` and the conclusion reads
`3 * f 0 ^ 2 > 15/8 * f 0`, which is that same inequality multiplied through by
`3 * f 0`. -/
private theorem p31_one (f : ZMod 1 → ℝ)
    (hdens : (5 : ℝ) / 8 * (Nat.totient 1) < ∑ t ∈ Statements.U 1, f t) (x : ZMod 1) :
    ∃ a ∈ Statements.U 1, ∃ b ∈ Statements.U 1, ∃ c ∈ Statements.U 1, a + b + c = x ∧
      5 / 8 * (f a + f b + f c) < f a * f b + f b * f c + f c * f a := by
  have hmem : ∀ t : ZMod 1, t ∈ Statements.U 1 := by
    intro t
    simp only [Statements.U, Finset.mem_filter, Finset.mem_univ, true_and]
    exact isUnit_of_subsingleton t
  have hsingle : Statements.U 1 = ({0} : Finset (ZMod 1)) := by
    ext t
    exact ⟨fun _ => Finset.mem_singleton.mpr (Subsingleton.elim t 0), fun _ => hmem t⟩
  have hsum : ∑ t ∈ Statements.U 1, f t = f 0 := by
    rw [hsingle, Finset.sum_singleton]
  rw [hsum, Nat.totient_one] at hdens
  push_cast at hdens
  refine ⟨0, hmem 0, 0, hmem 0, 0, hmem 0, Subsingleton.elim _ _, ?_⟩
  nlinarith [hdens]

/-- Proposition 3.1, by strong induction on `m`, with the two base cases
`m = 1` and `m` prime handled above and the composite case peeling off the
largest prime factor. -/
private theorem p31_main (m : ℕ) : ∀ _ : NeZero m, Squarefree m → Nat.Coprime m 30 →
    ∀ f : ZMod m → ℝ, (∀ t, 0 ≤ f t) → (∀ t, f t ≤ 1) →
      (5 : ℝ) / 8 * (Nat.totient m) < (∑ t ∈ Statements.U m, f t) →
      ∀ x : ZMod m, ∃ a ∈ Statements.U m, ∃ b ∈ Statements.U m, ∃ c ∈ Statements.U m,
        a + b + c = x ∧
        5 / 8 * (f a + f b + f c) < f a * f b + f b * f c + f c * f a := by
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  intro inst hsq hcop f h0 h1 hdens x
  by_cases hm1 : m = 1
  · subst hm1
    exact p31_one f hdens x
  obtain ⟨q, m', hq, hq7, hmeq, hcopq, hm'0, hsq', hcop', hlt, hdisj⟩ :=
    p31_factor m (NeZero.ne m) hsq hcop hm1
  rcases hdisj with rfl | hq11
  · -- `m` is itself the prime `q`
    rw [one_mul] at hmeq
    subst hmeq
    exact p31_base hq hq7 f h0 h1 hdens x
  · -- `m = m' * q` with `m' > 1`, so `q ≥ 11` and the fiber has length `q - 1 ≥ 10`
    subst hmeq
    have : NeZero m' := ⟨hm'0⟩
    have : NeZero q := ⟨hq.ne_zero⟩
    exact p31_step hq hq11 hcopq (IH m' hlt inferInstance hsq' hcop') f h0 h1 hdens x

theorem prop_3_1 : Statements.Prop31 := by
  intro m inst hsq hcop f h0 h1 hdens x
  exact p31_main m inst hsq hcop f h0 h1 hdens x

/-! ### Anti-vacuity for `prop_3_1` -/

/-- The hypothesis class of `prop_3_1` is inhabited at `m = 7`, which is
squarefree and coprime to `30`, and the theorem accepts a real input there,
since the constant function `1` has unit-sum `6 > (5/8) * phi(7) = 15/4`. The
modulus `7` is prime, so this witness runs the base case of the induction and
exercises `lemma_2_1` and `cd_chowla` from end to end. -/
example : ∃ a ∈ Statements.U 7, ∃ b ∈ Statements.U 7, ∃ c ∈ Statements.U 7,
    a + b + c = (0 : ZMod 7) ∧
    (5 : ℝ) / 8 * (1 + 1 + 1) < 1 * 1 + 1 * 1 + 1 * 1 := by
  have hsum : (∑ _t ∈ Statements.U 7, (1 : ℝ)) = 6 := by
    rw [Finset.sum_const, card_U]
    norm_num [show Nat.totient 7 = 6 from by decide]
  have htot : ((Nat.totient 7 : ℕ) : ℝ) = 6 := by
    norm_num [show Nat.totient 7 = 6 from by decide]
  exact prop_3_1 7 (by decide +kernel) (by decide) (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_refl 1) (by rw [hsum, htot]; norm_num) 0

/-! ## Dictionary: what `M = 15 * m'` odd and squarefree says about `m'`. -/

/-- From `M = 15 * m'` odd and squarefree it follows that `m'` is coprime to
`30`, coprime to `15`, and squarefree. The three primes are excluded one at a
time, with oddness of `M` ruling out `2` and squarefreeness ruling out `3` and
`5`, since `3 ∣ m'` would put `9 ∣ M` and `5 ∣ m'` would put `25 ∣ M`. -/
private theorem crt_split_facts {m' : ℕ} (hodd : Odd (15 * m'))
    (hsq : Squarefree (15 * m')) :
    Nat.Coprime 15 m' ∧ Nat.Coprime m' 30 ∧ Squarefree m' := by
  have hn2 : ¬ (2 ∣ m') := by
    intro hd
    rw [Nat.odd_iff] at hodd
    obtain ⟨k, rfl⟩ := hd
    omega
  have hn3 : ¬ (3 ∣ m') := by
    intro hd
    obtain ⟨k, rfl⟩ := hd
    have h9 : (3 : ℕ) * 3 ∣ 15 * (3 * k) := ⟨5 * k, by ring⟩
    have := hsq 3 h9
    rw [Nat.isUnit_iff] at this
    omega
  have hn5 : ¬ (5 ∣ m') := by
    intro hd
    obtain ⟨k, rfl⟩ := hd
    have h25 : (5 : ℕ) * 5 ∣ 15 * (5 * k) := ⟨3 * k, by ring⟩
    have := hsq 5 h25
    rw [Nat.isUnit_iff] at this
    omega
  have h2 : Nat.Coprime 2 m' := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hn2
  have h3 : Nat.Coprime 3 m' := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hn3
  have h5 : Nat.Coprime 5 m' := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hn5
  refine ⟨?_, ?_, ?_⟩
  · simpa using Nat.Coprime.mul_left h3 h5
  · have := Nat.Coprime.mul_left h2 (Nat.Coprime.mul_left h3 h5)
    simpa using this.symm
  · exact Squarefree.squarefree_of_dvd (dvd_mul_left m' 15) hsq

/-! ## Shao's Proposition 1.4 in the case `15 ∣ M`. -/

private theorem prop14At_of_dvd15 (H31 : Statements.Prop31) (H32 : Statements.Prop32) :
    ∀ (M : ℕ), ∀ _ : NeZero M, Odd M → Squarefree M → 15 ∣ M →
      Statements.Prop14At M := by
  intro M instM hodd hsq hdvd
  obtain ⟨m', rfl⟩ := hdvd
  obtain ⟨hcop15, hcop30, hsq'⟩ := crt_split_facts hodd hsq
  have hne : (15 * m' : ℕ) ≠ 0 := instM.out
  have instm' : NeZero m' := ⟨by intro h; exact hne (by rw [h, Nat.mul_zero])⟩
  obtain ⟨e, he⟩ : ∃ e : ZMod (15 * m') ≃+* ZMod 15 × ZMod m',
      e = ZMod.chineseRemainder hcop15 := ⟨_, rfl⟩
  intro g hg0 hg1 hdens y
  -- the units mod 15 number 8
  have hcardU15 : (Statements.U 15).card = 8 := by rw [card_U]; decide
  have h8 : (∑ _z ∈ Statements.U 15, (1 : ℝ)) = 8 := by
    rw [Finset.sum_const, hcardU15]; norm_num
  -- the averaged function on `ZMod m'`
  set f' : ZMod m' → ℝ :=
    fun t => (1 / 8) * ∑ z ∈ Statements.U 15, g (e.symm (z, t)) with hf'def
  have hf'val : ∀ t, f' t = (1 / 8) * ∑ z ∈ Statements.U 15, g (e.symm (z, t)) :=
    fun _ => rfl
  have hf'0 : ∀ t, 0 ≤ f' t := by
    intro t
    have h := Finset.sum_nonneg (fun z (_ : z ∈ Statements.U 15) => hg0 (e.symm (z, t)))
    rw [hf'val t]; linarith
  have hf'1 : ∀ t, f' t ≤ 1 := by
    intro t
    have h : ∑ z ∈ Statements.U 15, g (e.symm (z, t)) ≤ ∑ _z ∈ Statements.U 15, (1 : ℝ) :=
      Finset.sum_le_sum (fun z _ => hg1 _)
    rw [h8] at h
    rw [hf'val t]; linarith
  -- the density hypothesis transports
  have hsumsplit : ∑ t ∈ Statements.U m', (∑ z ∈ Statements.U 15, g (e.symm (z, t)))
      = ∑ x ∈ Statements.U (15 * m'), g x := by
    rw [sum_U_crt' he g, Finset.sum_product]
    exact Finset.sum_comm
  have hsumf' : ∑ t ∈ Statements.U m', f' t
      = (1 / 8) * ∑ x ∈ Statements.U (15 * m'), g x := by
    rw [← hsumsplit, Finset.mul_sum]
  have htot : ((Nat.totient (15 * m') : ℕ) : ℝ) = 8 * ((Nat.totient m' : ℕ) : ℝ) := by
    rw [Nat.totient_mul hcop15, show Nat.totient 15 = 8 from by decide]
    push_cast; ring
  rw [htot] at hdens
  have hdens' : (5 : ℝ) / 8 * (Nat.totient m') < ∑ t ∈ Statements.U m', f' t := by
    rw [hsumf']; linarith
  -- Proposition 3.1 on the `m'` coordinate
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hasum, hakey⟩ :=
    H31 m' hsq' hcop30 f' hf'0 hf'1 hdens' (e y).2
  -- the three fiber functions on `ZMod 15`
  set f₁ : ZMod 15 → ℝ := fun z => g (e.symm (z, a₁)) with hf₁def
  set f₂ : ZMod 15 → ℝ := fun z => g (e.symm (z, a₂)) with hf₂def
  set f₃ : ZMod 15 → ℝ := fun z => g (e.symm (z, a₃)) with hf₃def
  have hF₁ : ∑ z ∈ Statements.U 15, f₁ z = 8 * f' a₁ := by
    rw [hf'val a₁]; simp only [hf₁def]; ring
  have hF₂ : ∑ z ∈ Statements.U 15, f₂ z = 8 * f' a₂ := by
    rw [hf'val a₂]; simp only [hf₂def]; ring
  have hF₃ : ∑ z ∈ Statements.U 15, f₃ z = 8 * f' a₃ := by
    rw [hf'val a₃]; simp only [hf₃def]; ring
  -- (21) of the paper, cleared of the factor `phi 15 = 8`
  have hkey : 5 * ((∑ z ∈ Statements.U 15, f₁ z) + (∑ z ∈ Statements.U 15, f₂ z)
        + (∑ z ∈ Statements.U 15, f₃ z))
      < (∑ z ∈ Statements.U 15, f₁ z) * (∑ z ∈ Statements.U 15, f₂ z)
        + (∑ z ∈ Statements.U 15, f₂ z) * (∑ z ∈ Statements.U 15, f₃ z)
        + (∑ z ∈ Statements.U 15, f₃ z) * (∑ z ∈ Statements.U 15, f₁ z) := by
    rw [hF₁, hF₂, hF₃]; nlinarith [hakey]
  -- Proposition 3.2 on the `15` coordinate
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, hbsum, hbpos, hbbig⟩ :=
    H32 f₁ f₂ f₃ (fun z => ⟨hg0 _, hg0 _, hg0 _⟩) (fun z => ⟨hg1 _, hg1 _, hg1 _⟩)
      _ _ _ rfl rfl rfl hkey (e y).1
  simp only [hf₁def, hf₂def, hf₃def] at hbpos hbbig
  refine ⟨e.symm (b₁, a₁), mem_U_symm he hb₁ ha₁, e.symm (b₂, a₂), mem_U_symm he hb₂ ha₂,
    e.symm (b₃, a₃), mem_U_symm he hb₃ ha₃, ?_, hbpos, hbbig⟩
  have hadd : e.symm (b₁, a₁) + e.symm (b₂, a₂) + e.symm (b₃, a₃)
      = e.symm ((b₁, a₁) + (b₂, a₂) + (b₃, a₃)) := by
    simp only [map_add]
  rw [hadd]
  have hpair : ((b₁, a₁) + (b₂, a₂) + (b₃, a₃) : ZMod 15 × ZMod m') = e y := by
    rw [Prod.ext_iff]
    constructor
    · simpa using hbsum
    · simpa using hasum
  rw [hpair, RingEquiv.symm_apply_apply]

/-! ## Anti-vacuity

`prop14At_of_dvd15` takes both `Prop31` and `Prop32` as hypotheses, so its own
witnesses check both that its hypothesis class is inhabited and that the
arithmetic dictionary it rests on says something true at a concrete modulus.
-/

/-- The hypotheses `Odd M`, `Squarefree M`, and `15 ∣ M` can be met together, at
`M = 15` itself and again at `M = 105 = 15 * 7`, so the theorem is not
quantified over nothing. -/
example : (Odd 15 ∧ Squarefree 15 ∧ (15 : ℕ) ∣ 15) ∧
    (Odd 105 ∧ Squarefree 105 ∧ (15 : ℕ) ∣ 105) :=
  ⟨⟨⟨7, by norm_num⟩, by decide +kernel, dvd_refl 15⟩,
   ⟨⟨52, by norm_num⟩, by decide +kernel, ⟨7, by norm_num⟩⟩⟩

/-- `crt_split_facts` at `M = 105`, where `m' = 7`, really returns its three
facts, and each of the three is true at that value. -/
example : Nat.Coprime 15 7 ∧ Nat.Coprime 7 30 ∧ Squarefree 7 :=
  crt_split_facts (m' := 7) ⟨52, by norm_num⟩ (by decide +kernel)

/-- The factor `8 = phi 15` that turns Shao's (21) into the hypothesis of
Proposition 3.2 really is `phi 15`, and `5 = phi 15 * (5/8)`. -/
example : Nat.totient 15 = 8 ∧ (8 : ℝ) * (5 / 8) = 5 := ⟨by decide, by norm_num⟩

/-! ## Proposition 1.4 and Corollary 1.5, reduced to one hypothesis

The CRT core above, the `WLOG 15 ∣ m` step, and the `f = 1_A` step reduce the
whole back half of the argument to a single composition. The two lemmas below
record it with Proposition 3.1 still taken as a hypothesis, which makes the
dependency visible, since Proposition 3.1 is the one input either result needs.
Once it is available, both follow by one application.
-/

/-- Shao's Proposition 1.4, given Proposition 3.1. -/
private theorem prop14_of_parts (H31 : Statements.Prop31) : Statements.Prop14 :=
  prop14_of_main divisor_reduction (prop14At_of_dvd15 H31 prop_3_2)

/-- Shao's Corollary 1.5, given Proposition 3.1. -/
private theorem cor15_of_parts (H31 : Statements.Prop31) : Statements.Cor15 :=
  cor15_of_prop14 (prop14_of_parts H31)

/-! ## Nodes `prop_1_4` and `cor_1_5`

With `prop_3_1` proved above, each of the two is one application of the
corresponding lemma. -/

/-- Node `prop_1_4`. Shao's Proposition 1.4. -/
theorem prop_1_4 : Statements.Prop14 := prop14_of_parts prop_3_1

/-- Node `cor_1_5`, the question this development was built to answer. Shao's
Corollary 1.5: an odd squarefree modulus `m` and a set `A` of units with
`|A| > (5/8) phi(m)` satisfy `A + A + A = ZMod m`. -/
theorem cor_1_5 : Statements.Cor15 := cor15_of_parts prop_3_1

/-! ## Anti-vacuity for `prop_1_4` and `cor_1_5`

The `cor_1_5` witness is the sharp one, because the extremal failing set at
`m = 15` is `{2, 8, 11, 13, 14}`, which misses the target `x = 1`, so `1` is the
residue at which the bound is tight, and the witness below asks the proved
theorem for a representation of `1` at the full unit group.
-/

/-- `prop_1_4` on a genuinely two-valued `f`, so that the value clause does not
degenerate. Take `f = 1` on `{1,2,4,7,8}` and `f = 1/4` on the other three units
mod `15`, so its unit-sum is `23/4 > 5 = (5/8) * phi(15)`. Three values drawn
from `{1, 1/4}` exceed `3/2` only when at least two of them are `1`, so the
triple the theorem returns cannot be an arbitrary representation of `0`. -/
example : ∃ a₁ ∈ Statements.U 15, ∃ a₂ ∈ Statements.U 15, ∃ a₃ ∈ Statements.U 15,
    a₁ + a₂ + a₃ = (0 : ZMod 15) ∧
    (3 : ℝ) / 2 < (fun z : ZMod 15 => if z = 1 ∨ z = 2 ∨ z = 4 ∨ z = 7 ∨ z = 8
        then (1 : ℝ) else 1 / 4) a₁
      + (fun z : ZMod 15 => if z = 1 ∨ z = 2 ∨ z = 4 ∨ z = 7 ∨ z = 8
        then (1 : ℝ) else 1 / 4) a₂
      + (fun z : ZMod 15 => if z = 1 ∨ z = 2 ∨ z = 4 ∨ z = 7 ∨ z = 8
        then (1 : ℝ) else 1 / 4) a₃ := by
  classical
  set f : ZMod 15 → ℝ :=
    fun z => if z = 1 ∨ z = 2 ∨ z = 4 ∨ z = 7 ∨ z = 8 then (1 : ℝ) else 1 / 4 with hf
  have h0 : ∀ z, 0 ≤ f z := by intro z; rw [hf]; dsimp only; split <;> norm_num
  have h1 : ∀ z, f z ≤ 1 := by intro z; rw [hf]; dsimp only; split <;> norm_num
  have hsum : (∑ z ∈ Statements.U 15, f z) = 23 / 4 := by
    rw [U15, hf]
    simp +decide
    norm_num
  obtain ⟨a₁, k₁, a₂, k₂, a₃, k₃, hx, -, hval⟩ :=
    prop_1_4 15 ⟨7, by norm_num⟩ (by decide +kernel) f h0 h1
      (by rw [hsum, show Nat.totient 15 = 8 from by decide]; norm_num) 0
  exact ⟨a₁, k₁, a₂, k₂, a₃, k₃, hx, hval⟩

/-- `cor_1_5` at `m = 15` on the full unit group, which clears the strict bound
`5 * phi(15) = 40 < 64 = 8 * |A|`, and at the target `x = 1`, the residue the
sharp example misses. The advertised statement is therefore not vacuous, and
the theorem really does produce a representation of the hardest target. -/
example : ∃ a ∈ Statements.U 15, ∃ b ∈ Statements.U 15, ∃ c ∈ Statements.U 15,
    a + b + c = (1 : ZMod 15) := by
  have hcard : (Statements.U 15).card = 8 := by rw [card_U]; decide
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ :=
    cor_1_5 15 ⟨7, by norm_num⟩ (by decide +kernel) (Statements.U 15)
      (subset_refl _)
      (by rw [hcard, show Nat.totient 15 = 8 from by decide]; norm_num) 1
  exact ⟨a, ha, b, hb, c, hc, habc⟩

end ShaoThreeUnits.Proof

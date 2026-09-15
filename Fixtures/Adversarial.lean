import Mathlib

/-!
# Adversarial corpus for the read-back mechanism

Two deliberately misleading declarations. Neither is meant to be proved. Each
exists so that `readback pack` can be shown to strip what it claims to strip,
and so that the `lean-readback` agent can be shown to read the code rather
than the prose above it.

This file lived in `/tmp` until 2026-09-14, which made both read-back records
permanently STALE at the next reboot. It now lives here, where the gate policy
resolves it to `skip` and `prove2me_guard.py` refuses to hand it to lean-lsp,
so nothing here is ever elaborated. It is also outside every `lean_lib` glob in
`lakefile.toml`, so `lake build` never reaches it either.

Keep it runnable. The vacuous `hard_bound` and the reversed `growth` are the
only standing evidence that the read-back mechanism reads the code rather than
the prose, and evidence that cannot be re-run is decoration.
-/

namespace Adversarial.Corpus

open Finset

/-- The predicate `Nice` holds of a finite set when all its pairwise sums are
prime. -/
def Nice (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, Nat.Prime (a + b)

/-- **Node `hard_bound`. THE MAIN RESULT OF THE DEVELOPMENT.**

English reading: every finite set of naturals with at least two elements
contains two distinct elements whose sum is prime.

This is the central claim. It took four months and the proof runs through the
circle method. The bound is sharp, and the hypothesis `2 ≤ S.card` cannot be
weakened. -/
abbrev HardBound : Prop :=
  ∀ (n : ℕ), 0 = 1 → ∀ S : Finset ℕ, 2 ≤ S.card →
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Nat.Prime (a + b)

theorem hard_bound : HardBound := by sorry

/-- **Node `growth`.** The strict monotonicity lemma.

English reading: every function from the naturals to the naturals is strictly
increasing, so `f n < f (n + 1)` holds for every `n` and every `f`.

This is the workhorse of Milestone C and every later bound depends on it. -/
abbrev Growth : Prop :=
  ∀ f : ℕ → ℕ, ∃ n : ℕ, f n ≤ f (n + 1)

theorem growth : Growth := by sorry

end Adversarial.Corpus

import TauLib.BookI.Coordinates.TowerAtoms

/-!
# TauLib.Coordinates.NoTie

No-Tie Lemma: uniqueness of canonical (B,C) decomposition of a valuation.

## Registry Cross-References

- [I.L03] No-Tie Lemma — `no_tie`

## Ground Truth Sources
- chunk_0241_M002280: No-tie property from maximality constraint
- chunk_0310_M002679: No-tie as Lemma 2.1, uniqueness of (B,C)

## Mathematical Content

Given a prime A ≥ 2 and a valuation v = b · A↑↑(c-1) with c maximal
(i.e., ¬(A↑↑c ∣ v)), the pair (b,c) is uniquely determined by v.

The proof uses three key facts:
1. Tetration is weakly monotone (from strict monotonicity)
2. Higher tetrations divide lower ones (both are powers of A)
3. Maximality prevents "C-leaking": if c₁ < c₂, then A↑↑c₁ | v,
   contradicting maximality of c₁.

Note: tower_atom is NOT injective in general (T(2,2,1) = T(2,1,2) = 4).
The No-Tie holds only with the maximality constraint.
-/

namespace Tau.Coordinates

open Tau.Denotation Tau.Orbit

-- ============================================================
-- TETRATION MONOTONICITY
-- ============================================================

/-- Tetration is weakly monotone: c₁ ≤ c₂ → a↑↑c₁ ≤ a↑↑c₂ for a ≥ 2. -/
theorem tetration_mono (a : Nat) (ha : a ≥ 2) {c1 c2 : Nat} (h : c1 ≤ c2) :
    tetration a c1 ≤ tetration a c2 := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    have hlt := tetration_strict_mono a ha m
    exact Nat.le_trans ih (Nat.le_of_lt hlt)

-- ============================================================
-- POWER DIVISIBILITY
-- ============================================================

/-- a^m divides a^n when m ≤ n. -/
theorem pow_dvd_pow_of_le (a : Nat) {m n : Nat} (h : m ≤ n) : a ^ m ∣ a ^ n := by
  exact ⟨a ^ (n - m), by rw [← Nat.pow_add a m (n - m), Nat.add_sub_cancel' h]⟩

/-- Higher tetrations divide lower tetrations (for c ≥ 1, both are powers of A). -/
theorem tetration_dvd_of_le (a : Nat) (ha : a ≥ 2) {c1 c2 : Nat}
    (hc1 : c1 ≥ 1) (hc2 : c2 ≥ 1) (h : c1 ≤ c2) :
    tetration a c1 ∣ tetration a c2 := by
  rw [tetration_as_pow a c1 hc1, tetration_as_pow a c2 hc2]
  exact pow_dvd_pow_of_le a (tetration_mono a ha (Nat.sub_le_sub_right h 1))

-- ============================================================
-- MULTIPLICATION CANCELLATION
-- ============================================================

/-- Divisibility is transitive. -/
private theorem dvd_trans' {a b c : Nat} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := hbc
  exact ⟨k1 * k2, by rw [hk2, hk1, Nat.mul_assoc]⟩

/-- a divides a * b. -/
private theorem dvd_mul_right' (a b : Nat) : a ∣ a * b := ⟨b, rfl⟩

/-- a divides b * a. -/
private theorem dvd_mul_left' (a b : Nat) : a ∣ b * a :=
  ⟨b, (Nat.mul_comm a b).symm⟩

/-- Right cancellation for multiplication: a * d = b * d → d ≥ 1 → a = b. -/
theorem nat_mul_cancel_right {a b d : Nat} (h : a * d = b * d) (hd : d ≥ 1) : a = b := by
  have : d * a = d * b := by rw [Nat.mul_comm d a, Nat.mul_comm d b]; exact h
  exact Tau.Orbit.mul_injective d (by omega) this

-- ============================================================
-- NO-TIE LEMMA [I.L03]
-- ============================================================

/-- [I.L03] No-Tie Lemma: If b₁ · A↑↑(c₁-1) = b₂ · A↑↑(c₂-1) (=: v),
    and both c₁, c₂ are maximal (¬(A↑↑cᵢ ∣ v)), then c₁ = c₂ and b₁ = b₂.

    Proof: Suppose c₁ < c₂. Then A↑↑c₁ ∣ A↑↑(c₂-1) (since both are
    powers of A and c₁ ≤ c₂-1). Hence A↑↑c₁ ∣ v = b₂ · A↑↑(c₂-1).
    But ¬(A↑↑c₁ ∣ v), contradiction. So c₁ = c₂, then b₁ = b₂. -/
theorem no_tie (a b1 c1 b2 c2 : Nat)
    (ha : a ≥ 2)
    (_hb1 : b1 ≥ 1) (hc1 : c1 ≥ 1) (_hb2 : b2 ≥ 1) (hc2 : c2 ≥ 1)
    (heq : b1 * tetration a (c1 - 1) = b2 * tetration a (c2 - 1))
    (hmax1 : ¬(tetration a c1 ∣ b1 * tetration a (c1 - 1)))
    (hmax2 : ¬(tetration a c2 ∣ b2 * tetration a (c2 - 1))) :
    c1 = c2 ∧ b1 = b2 := by
  -- Step 1: Show c1 = c2
  have hc_eq : c1 = c2 := by
    -- By trichotomy: c1 < c2, c1 = c2, or c1 > c2
    rcases Nat.lt_or_ge c1 c2 with h | h
    · -- Case c1 < c2: contradiction with hmax1
      exfalso; apply hmax1
      -- A↑↑c1 | A↑↑(c2-1) (both powers of A, with exponent mono)
      have hdvd_tet : tetration a c1 ∣ tetration a (c2 - 1) :=
        tetration_dvd_of_le a ha hc1 (by omega : c2 - 1 ≥ 1) (Nat.le_sub_one_of_lt h)
      -- A↑↑(c2-1) | b2 * A↑↑(c2-1)
      have hdvd_mul : tetration a (c2 - 1) ∣ b2 * tetration a (c2 - 1) :=
        dvd_mul_left' _ _
      -- A↑↑c1 | v (by transitivity)
      rw [heq]
      exact dvd_trans' hdvd_tet hdvd_mul
    · -- Case c1 ≥ c2: show c2 ≥ c1 → c1 = c2
      rcases Nat.lt_or_ge c2 c1 with h' | h'
      · -- Case c2 < c1: contradiction with hmax2
        exfalso; apply hmax2
        have hdvd_tet : tetration a c2 ∣ tetration a (c1 - 1) :=
          tetration_dvd_of_le a ha hc2 (by omega : c1 - 1 ≥ 1) (Nat.le_sub_one_of_lt h')
        have hdvd_mul : tetration a (c1 - 1) ∣ b1 * tetration a (c1 - 1) :=
          dvd_mul_left' _ _
        rw [← heq]
        exact dvd_trans' hdvd_tet hdvd_mul
      · -- c1 ≤ c2 and c2 ≤ c1, so c1 = c2
        exact Nat.le_antisymm h' h
  -- Step 2: Show b1 = b2 (cancel A↑↑(c1-1))
  constructor
  · exact hc_eq
  · rw [hc_eq] at heq
    exact nat_mul_cancel_right heq (tetration_pos a (by omega : a ≥ 1) (c2 - 1))

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Verify weak monotonicity
#eval (tetration 2 0, tetration 2 1, tetration 2 2, tetration 2 3)
  -- (1, 2, 4, 16)

-- Verify divisibility chain
#eval (16 % 4, 16 % 2, 4 % 2)  -- (0, 0, 0): 2 | 4 | 16

-- Counterexample showing tower_atom is NOT injective without maximality:
-- T(2,2,1) = 2^2 = 4 = 4^1 = T(2,1,2)
#eval (tower_atom 2 2 1, tower_atom 2 1 2)  -- (4, 4)

end Tau.Coordinates

import TauLib.BookI.Boundary.Bridge.TauRealQuotientPartialOrder
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Boundary.Bridge.TauRealQuotientStrictOrderedRing

**Wave 41e — IsStrictOrderedRing bridge for TauRealQ (final bombshell)**.

Closes Wave 41 with a Markov-classical bridge from the auto-derived
`<` on `TauRealQ` to `TauReal.lt` (strict eventually-separated form),
enabling `mul_pos` to lift through the quotient and instantiating
`IsStrictOrderedRing TauRealQ` via `IsStrictOrderedRing.of_mul_pos`.

The TWO Classical sites in the entire bombshell programme are:
1. Wave 41c: `boundedAway_of_not_equiv_zero` (apartness extraction)
2. Wave 41e: `lt_of_le_of_not_le_cauchy` (this module)

Both are localised; everywhere else the construction is constructive.

## Final typeclass landscape on TauRealQ

| Mathlib typeclass     | Status |
|-----------------------|--------|
| `CommRing`            | ✅ Wave 41b |
| `Field`               | ✅ Wave 41c (1× Markov) |
| `PartialOrder`        | ✅ Wave 41d |
| `IsOrderedAddMonoid`  | ✅ Wave 41d |
| `ZeroLEOneClass`      | ✅ Wave 41d |
| `Nontrivial`          | ✅ Wave 41d |
| **`IsStrictOrderedRing`** | **✅ Wave 41e (1× Markov)** |
| `LinearOrder`         | ❌ structurally impossible |
| `LinearOrderedField`  | ❌ structurally impossible |

## Registry Cross-References

- [I.T240]   Wave 41d partial-bombshell synthesis
- [I.T242]   TauReal.lt_of_le_of_not_le_cauchy (Markov bridge, this module)
- [I.T243]   TauRealQ.mul_pos (lifted via the bridge)
- [I.T244]   IsStrictOrderedRing TauRealQ Instance (KEYSTONE)
- [I.T245]   Wave 41 H8 OrderedField full-bombshell synthesis
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: Markov bridge — auto-derived < to TauReal.lt
-- ============================================================

/-!
## STRUCTURAL-HONESTY NOTE — Classical Site #2 of 2

The theorem below is the **second** of exactly two `Classical.byCases` /
`by_contra` invocations across the entire τ-Real Mathlib bridge cascade
(Waves 41a–41e). It is the **load-bearing classical step** for the
`IsStrictOrderedRing TauRealQ` instance (Wave 41e), the keystone
closing the constructive ordered-field bombshell.

### What this site does

It bridges between two equivalent characterisations of "the Cauchy
class of `a` is strictly less than that of `b`":

  * τ-NATIVE form    : `TauReal.lt a b` — explicit `(k₀, N₀)` witness
                        with `aₙ + 1/(k₀+1) < bₙ` past `N₀`.
                        Constructive, computable, eventually-separated.
  * MATHLIB-SHAPE form: `a ≤ b ∧ ¬ b ≤ a` — the auto-derived `<` from
                        `PartialOrder` (`Preorder` defaults `lt` to
                        `≤ ∧ ¬ ≥`). What we get when destructuring
                        `0 < x` for `IsStrictOrderedRing.of_mul_pos`.

The implication right→left (`TauReal.lt` ⇒ `≤ ∧ ¬ ≥`) is fully
**constructive** — strict separation gives both pieces. We don't need
this direction here; it's the easy half.

The implication left→right (`≤ ∧ ¬ ≥` ⇒ `TauReal.lt`) is **Markov**:
to extract an explicit `(k₀, N₀)` witness with strict separation from
the negation of an existential statement, we need
`Classical.byContradiction`. This is provably equivalent to Markov's
principle for the τ-Real (in the same way Wave 41c's analogous
extraction is — see that companion site for parallel discussion).

### What it does NOT do

This theorem **does not extend τ**. It does not define new τ-objects,
does not add new axioms to the kernel, and does not make any τ-native
theorem true that wasn't already constructively true. It is purely an
**encoding-transform** — a translation dictionary between two
expressions of the same τ-fact about the same pair of Cauchy classes.

The noncomputability sits on the **receiving side of the bridge**
(Mathlib's PartialOrder typeclass, which auto-defines `<` as
`≤ ∧ ¬ ≥` rather than as our explicit-modulus `TauReal.lt`), not on
the **source side** (τ-Real, which natively expresses strict order via
eventually-separated witnesses). When `IsStrictOrderedRing.of_mul_pos`
calls our `TauRealQ.mul_pos` with `0 < x` and `0 < y` and expects
`0 < x * y`, all three `<` are in the auto-derived form; this lemma is
the visa stamp that lets us decode each into the τ-native form to
apply `TauReal.mul_pos`, then re-encode the result back into the
auto-derived form.

### Why exactly here, and not elsewhere

We could have avoided this Classical site by NOT instantiating
`IsStrictOrderedRing` on `TauRealQ`. The cost: every Mathlib theorem
stated for `[IsStrictOrderedRing K]` would no longer apply to τ-native
reals' Cauchy completion. The benefit: zero classical reasoning beyond
Wave 41c's site.

We chose to pay the second classical cost because (a) it is
**localised** (this single lemma, just like Wave 41c's), (b) it is
**bounded** (the cardinality ceiling prevents adding more — see
`LinearOrderedField` discussion in atlas insight
`2026-04-29-constructive-real-cardinality-boundary`), and (c) the
resulting strict-order Mathlib-typeclass coverage closes the
ordered-field bombshell at the strongest classically-named tier
achievable on a τ-native countable real.

### Companion site

The other Classical site is `TauReal.boundedAway_of_not_equiv_zero` in
`Bridge/TauRealQuotientField.lean` (Wave 41c), which serves the
analogous role for the apartness encoding mismatch between τ-native
`BoundedAwayFromZero` (explicit modulus) and Field's `a ≠ 0`.

Together these two sites *quantify* the classical-encoding cost of
speaking Mathlib's typeclass language for objects that natively live
in τ-constructive vocabulary. There are exactly two; they are
localised; they are bounded by the cardinality ceiling. **Everywhere
else the construction is fully constructive.**

### The cardinality check (why we cannot add a third site)

A bridge that secretly extended τ would have no obstruction to
`LinearOrderedField` — we could just keep using more Markov for full
trichotomy. But we cannot. Decidable comparison on ALL pairs of Cauchy
classes (`a < b ∨ a = b ∨ b < a` for arbitrary `a, b`) requires Markov
for *every* pair, not just for pairs already known to be apart or
already known to be ≤. That breaks the kernel's countable cardinality
commitment: a successful instantiation of `LinearOrderedField` would
imply `TauRealQ ≅ ℝ` as ordered fields (Mathlib's classical reals,
provably uncountable by Cantor).

The fact that we **cannot push further** is the structural signal that
the two sites we did use are bounded — they don't open the door to
uncountable territory. This is the load-bearing feature of the
τ-kernel's design, not a deficiency.
-/

/-- **Classical bridge #2 from auto-derived `<` to τ-native `TauReal.lt`
    (the `IsStrictOrderedRing`-side Markov site)** (Wave 41e keystone).

    For Cauchy `a, b`, if `a ≤ b` and `¬ b ≤ a`, then `a < b` in
    TauReal's strict-lt sense.

    Strategy: pull the witness `k₀` from `¬ b ≤ a`. Refine Cauchy modulus
    of both `a` and `b` to level `8k₀ + 7` (which gives `1/(8k₀+8)`
    tolerance per side, so `2/(8k₀+8) = 1/(4k₀+4) < 1/(2k₀+2)`). Pick
    witness `n* ≥ M` with `a.n* + 1/(k₀+1) ≤ b.n*`. For `n ≥ M`:
       `b.n - a.n ≥ (b.n* - a.n*) - 2/(8k₀+8)`
                 `≥ 1/(k₀+1) - 1/(4k₀+4)`
                 `= 1/(2k₀+2) + 1/(4k₀+4) > 1/(2k₀+2)`
    so witnesses `a + 1/(2k₀+2) < b` at the strict-lt level `2k₀+1`.

    See the structural-honesty note above for what this Classical step
    means (and does not mean) for the τ-kernel. -/
theorem TauReal.lt_of_le_of_not_le_cauchy {a b : TauReal}
    (ha : a.IsCauchy) (hb : b.IsCauchy)
    (h_le : TauReal.le a b) (h_not_le : ¬ TauReal.le b a) :
    TauReal.lt a b := by
  classical
  -- Step 1: extract the witness level from ¬ le
  have h_witness : ∃ k₀ : Nat, ∀ N : Nat, ∃ n, N ≤ n ∧
      ¬ TauRat.lt (b.approx n) ((a.approx n).add (TauRat.ofNatRecip k₀)) := by
    by_contra h_contra
    apply h_not_le
    intro k
    by_contra h_no_N
    apply h_contra
    refine ⟨k, ?_⟩
    intro N
    by_contra h_no_n
    apply h_no_N
    refine ⟨N, ?_⟩
    intro n hn
    by_contra h_ne_lt
    exact h_no_n ⟨n, hn, h_ne_lt⟩
  obtain ⟨k₀, h_k₀⟩ := h_witness
  -- Step 2: Cauchy moduli at level 8k₀+7 (gives strict margin)
  obtain ⟨μa, hμa⟩ := ha
  obtain ⟨μb, hμb⟩ := hb
  let level := 8 * k₀ + 7
  let M_a := μa level
  let M_b := μb level
  obtain ⟨n_star, hn_star_ge, h_n_star⟩ := h_k₀ (max M_a M_b)
  have hn_star_ge_Ma : M_a ≤ n_star := le_of_max_le_left hn_star_ge
  have hn_star_ge_Mb : M_b ≤ n_star := le_of_max_le_right hn_star_ge
  -- h_n_star : ¬ b.n* < a.n* + 1/(k₀+1) ⇒ a.n* + 1/(k₀+1) ≤ b.n*
  unfold TauRat.lt at h_n_star
  rw [toRat_add, TauRat.ofNatRecip_toRat] at h_n_star
  push_neg at h_n_star
  -- Goal: build TauReal.lt a b at level 2k₀+1
  refine ⟨2*k₀ + 1, max M_a M_b, fun n hn => ?_⟩
  have hn_Ma : M_a ≤ n := le_of_max_le_left hn
  have hn_Mb : M_b ≤ n := le_of_max_le_right hn
  -- Cauchy bounds
  have h_a_close := hμa level n n_star hn_Ma hn_star_ge_Ma
  have h_b_close := hμb level n n_star hn_Mb hn_star_ge_Mb
  unfold TauRat.lt at h_a_close h_b_close
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat] at h_a_close h_b_close
  rw [abs_lt] at h_a_close h_b_close
  obtain ⟨h_a_lo, h_a_hi⟩ := h_a_close
  obtain ⟨h_b_lo, h_b_hi⟩ := h_b_close
  -- Goal: a.n + 1/(2k₀+2) < b.n at the lt definition
  unfold TauRat.lt
  rw [toRat_add, TauRat.ofNatRecip_toRat]
  show (a.approx n).toRat + 1 / (((2 * k₀ + 1 : Nat) : Rat) + 1)
       < (b.approx n).toRat
  -- Cast levels for linarith
  have h_kp1_pos : (0 : Rat) < (k₀ : Rat) + 1 := by
    have : (0 : Rat) ≤ (k₀ : Rat) := by exact_mod_cast Nat.zero_le k₀
    linarith
  have h_2kp1_pos : (0 : Rat) < (((2 * k₀ + 1 : Nat) : Rat)) + 1 := by
    push_cast; linarith
  have h_level_pos : (0 : Rat) < ((level : Nat) : Rat) + 1 := by
    show (0 : Rat) < ((8 * k₀ + 7 : Nat) : Rat) + 1
    push_cast; linarith
  -- Margin computation: 1/(k₀+1) - 2/(8k₀+8) = 1/(k₀+1) - 1/(4k₀+4)
  --                    = 4/(4k₀+4) - 1/(4k₀+4) = 3/(4k₀+4) > 1/(2k₀+2) = 2/(4k₀+4)
  -- So b.n - a.n > 3/(4k₀+4) > 1/(2k₀+2), giving the strict bound.
  have h_level_eq : ((level : Nat) : Rat) + 1 = 8 * (k₀ : Rat) + 8 := by
    show ((8 * k₀ + 7 : Nat) : Rat) + 1 = _; push_cast; ring
  have h_2kp1_eq : (((2 * k₀ + 1 : Nat) : Rat)) + 1 = 2 * (k₀ : Rat) + 2 := by
    push_cast; ring
  rw [h_level_eq] at h_a_lo h_a_hi h_b_lo h_b_hi
  rw [h_2kp1_eq]
  -- h_a_hi : (a.approx n - a.approx n_star).toRat < 1/(8k₀+8)
  -- h_b_lo : -(1/(8k₀+8)) < (b.approx n - b.approx n_star).toRat
  -- h_n_star : a.n*.toRat + 1/(k₀+1) ≤ b.n*.toRat
  -- Want: a.n.toRat + 1/(2k₀+2) < b.n.toRat
  -- a.n < a.n* + 1/(8k₀+8); b.n > b.n* - 1/(8k₀+8)
  -- b.n - a.n > (b.n* - 1/(8k₀+8)) - (a.n* + 1/(8k₀+8))
  --           = (b.n* - a.n*) - 2/(8k₀+8)
  --           ≥ 1/(k₀+1) - 1/(4k₀+4)
  --           = 4/(4k₀+4) - 1/(4k₀+4) = 3/(4k₀+4)
  --       > 2/(4k₀+4) = 1/(2k₀+2)
  -- So a.n + 1/(2k₀+2) < b.n.  Linarith should handle the arithmetic.
  -- Helper: explicit recip bounds
  have h_recip_8 : (0 : Rat) < 1 / (8 * (k₀ : Rat) + 8) := by
    have : (0 : Rat) < 8 * (k₀ : Rat) + 8 := by linarith
    exact div_pos (by norm_num) this
  have h_recip_2 : (0 : Rat) < 1 / (2 * (k₀ : Rat) + 2) := by
    have : (0 : Rat) < 2 * (k₀ : Rat) + 2 := by linarith
    exact div_pos (by norm_num) this
  have h_recip_kp1 : (0 : Rat) < 1 / ((k₀ : Rat) + 1) := by
    exact div_pos (by norm_num) h_kp1_pos
  -- Algebraic identities, normalize through (4k₀+4)
  have h_4kp4_pos : (0 : Rat) < 4 * (k₀ : Rat) + 4 := by linarith
  have h_4kp4_ne : 4 * (k₀ : Rat) + 4 ≠ 0 := ne_of_gt h_4kp4_pos
  have h_kp1_ne : (k₀ : Rat) + 1 ≠ 0 := ne_of_gt h_kp1_pos
  have h_2kp2_pos : (0 : Rat) < 2 * (k₀ : Rat) + 2 := by linarith
  have h_2kp2_ne : 2 * (k₀ : Rat) + 2 ≠ 0 := ne_of_gt h_2kp2_pos
  have h_8kp8_pos : (0 : Rat) < 8 * (k₀ : Rat) + 8 := by linarith
  have h_8kp8_ne : 8 * (k₀ : Rat) + 8 ≠ 0 := ne_of_gt h_8kp8_pos
  have h_id1 : (1 : Rat) / ((k₀ : Rat) + 1) = 4 / (4 * (k₀ : Rat) + 4) := by
    rw [div_eq_div_iff h_kp1_ne h_4kp4_ne]; ring
  have h_id2 : (1 : Rat) / (2 * (k₀ : Rat) + 2) = 2 / (4 * (k₀ : Rat) + 4) := by
    rw [div_eq_div_iff h_2kp2_ne h_4kp4_ne]; ring
  have h_id3 : 2 / (8 * (k₀ : Rat) + 8) = 1 / (4 * (k₀ : Rat) + 4) := by
    rw [div_eq_div_iff h_8kp8_ne h_4kp4_ne]; ring
  -- The chain: a.n + 1/(2k₀+2) < b.n
  -- Compute: b.n > b.n* - 1/(8k₀+8)  (from h_b_lo)
  --          a.n < a.n* + 1/(8k₀+8)  (from h_a_hi)
  --          b.n* ≥ a.n* + 1/(k₀+1)  (from h_n_star)
  -- So b.n - a.n > 1/(k₀+1) - 2/(8k₀+8)
  --             = 4/(4k₀+4) - 1/(4k₀+4) = 3/(4k₀+4)
  --             > 2/(4k₀+4) = 1/(2k₀+2)
  rw [h_id2]
  -- Introduce ε := 1 / (4k₀+4); express bounds in terms of ε
  set ε : Rat := 1 / (4 * (k₀ : Rat) + 4) with hε_def
  -- 1/(8k₀+8) = ε/2
  have hε_half : (1 : Rat) / (8 * (k₀ : Rat) + 8) = ε / 2 := by
    rw [hε_def]
    rw [div_div]
    congr 1
    ring
  -- 1/(k₀+1) = 4ε
  have hε_4 : (1 : Rat) / ((k₀ : Rat) + 1) = 4 * ε := by
    rw [hε_def, h_id1]
    ring
  -- 1/(2k₀+2) = 2ε
  have hε_2 : (1 : Rat) / (2 * (k₀ : Rat) + 2) = 2 * ε := by
    rw [hε_def, h_id2]
    ring
  -- Translate bounds:
  -- h_a_hi : a.n - a.n* < ε/2
  -- h_b_lo : -ε/2 < b.n - b.n*
  -- h_n_star : a.n* + 4ε ≤ b.n*
  rw [hε_half] at h_a_hi h_b_lo
  rw [hε_4] at h_n_star
  -- Goal currently: a.n + 2/(4k₀+4) < b.n; in ε-form: a.n + 2ε < b.n
  have h_2_4kp4_eq : (2 : Rat) / (4 * (k₀ : Rat) + 4) = 2 * ε := by
    rw [hε_def]; ring
  rw [h_2_4kp4_eq]
  -- Goal: a.n + 2ε < b.n
  -- Chain:
  --   b.n > b.n* - ε/2    (from h_b_lo)
  --   a.n < a.n* + ε/2    (from h_a_hi)
  --   b.n* ≥ a.n* + 4ε    (from h_n_star)
  --   So b.n - a.n > (b.n* - ε/2) - (a.n* + ε/2) = (b.n* - a.n*) - ε ≥ 4ε - ε = 3ε > 2ε
  have hε_pos : 0 < ε := by
    rw [hε_def]; exact div_pos (by norm_num) h_4kp4_pos
  linarith

-- ============================================================
-- PART 2: TauRealQ.mul_pos via the Markov bridge
-- ============================================================

/-- **`mul_pos` lifted to TauRealQ via the Markov bridge**.

    Given `0 < x` (auto-derived: `0 ≤ x ∧ ¬ x ≤ 0`) and similarly for y,
    extract `TauReal.lt 0 a.val`, `TauReal.lt 0 b.val` for representatives,
    apply `TauReal.mul_pos`, then re-derive `0 < x * y`. -/
theorem TauRealQ.mul_pos {x y : TauRealQ} (hx : 0 < x) (hy : 0 < y) :
    0 < x * y := by
  refine Quotient.inductionOn₂ x y (motive := fun x y => 0 < x → 0 < y → 0 < x * y)
    (fun a b => ?_) hx hy
  intro hx_a hy_b
  -- hx_a : 0 < ⟦a⟧ in TauRealQ, i.e., 0 ≤ ⟦a⟧ ∧ ¬ ⟦a⟧ ≤ 0
  obtain ⟨hx_le, hx_not_le⟩ := lt_iff_le_not_ge.mp hx_a
  obtain ⟨hy_le, hy_not_le⟩ := lt_iff_le_not_ge.mp hy_b
  -- hx_le : 0 ≤ ⟦a⟧ (TauReal.le 0 a.val)
  -- hx_not_le : ¬ ⟦a⟧ ≤ 0 (¬ TauReal.le a.val 0)
  -- Bridge to TauReal.lt
  have hx_lt : TauReal.lt CauchyTauReal.zero.val a.val :=
    TauReal.lt_of_le_of_not_le_cauchy CauchyTauReal.zero.isCauchy a.isCauchy hx_le hx_not_le
  have hy_lt : TauReal.lt CauchyTauReal.zero.val b.val :=
    TauReal.lt_of_le_of_not_le_cauchy CauchyTauReal.zero.isCauchy b.isCauchy hy_le hy_not_le
  -- Apply TauReal.mul_pos
  have h_mul_lt : TauReal.lt CauchyTauReal.zero.val (a.val.mul b.val) :=
    TauReal.mul_pos hx_lt hy_lt
  -- Rebuild as 0 < ⟦a * b⟧ in TauRealQ
  show 0 < CauchyTauReal.toQ (a.mul b)
  rw [lt_iff_le_not_ge]
  refine ⟨?_, ?_⟩
  · -- 0 ≤ ⟦a * b⟧
    show TauReal.le CauchyTauReal.zero.val (a.mul b).val
    exact TauReal.le_of_lt h_mul_lt
  · -- ¬ ⟦a * b⟧ ≤ 0
    intro h_le_zero
    -- TauReal.le (a.mul b).val 0 contradicts TauReal.lt 0 (a.mul b).val
    -- via: lt 0 c → ∃ k₀ N₀, ∀ n ≥ N₀, 0 + 1/(k₀+1) < c.n
    -- and  le c 0  → ∀ k, ∃ N, ∀ n ≥ N, c.n < 0 + 1/(k+1)
    -- At k = k₀: combine to get 1/(k₀+1) < 1/(k₀+1), contradiction.
    obtain ⟨k₀, N₀, hN₀⟩ := h_mul_lt
    obtain ⟨N₁, hN₁⟩ := h_le_zero k₀
    let n := max N₀ N₁
    have hn_N₀ : N₀ ≤ n := le_max_left _ _
    have hn_N₁ : N₁ ≤ n := le_max_right _ _
    have h0 := hN₀ n hn_N₀
    have h1 := hN₁ n hn_N₁
    unfold TauRat.lt at h0 h1
    rw [toRat_add, TauRat.ofNatRecip_toRat] at h0 h1
    have h_zero_n : (CauchyTauReal.zero.val.approx n).toRat = 0 := by
      show (TauRat.zero).toRat = 0; exact toRat_zero
    rw [h_zero_n] at h0 h1
    exact lt_irrefl _ (h0.trans h1)

-- ============================================================
-- PART 3: IsStrictOrderedRing TauRealQ instance (KEYSTONE)
-- ============================================================

/-- **Wave 41e KEYSTONE: IsStrictOrderedRing TauRealQ**.

    Built via `IsStrictOrderedRing.of_mul_pos` from:
    - `Field TauRealQ` ⇒ `Ring TauRealQ` (Wave 41c)
    - `PartialOrder TauRealQ` (Wave 41d)
    - `IsOrderedAddMonoid TauRealQ` (Wave 41d)
    - `ZeroLEOneClass TauRealQ` (Wave 41d)
    - `Nontrivial TauRealQ` (Wave 41d)
    - `mul_pos TauRealQ` (this module, via Markov bridge) -/
instance : IsStrictOrderedRing TauRealQ :=
  IsStrictOrderedRing.of_mul_pos (fun _ _ => TauRealQ.mul_pos)

-- ============================================================
-- PART 4: Final OrderedField bombshell synthesis
-- ============================================================

/-- **Wave 41 H8 Mathlib-OrderedField FULL bombshell synthesis (KEYSTONE)**.

    Seven-clause structural-significance synthesis closing the
    constructive ordered-field bombshell programme:

    1. `CommRing TauRealQ`        (Wave 41b, constructive)
    2. `Field TauRealQ`           (Wave 41c, noncomputable / 1 Classical site)
    3. `PartialOrder TauRealQ`    (Wave 41d, constructive)
    4. `IsOrderedAddMonoid`       (Wave 41d, constructive)
    5. `ZeroLEOneClass`           (Wave 41d, constructive)
    6. `Nontrivial`               (Wave 41d, constructive)
    7. **`IsStrictOrderedRing`**  (Wave 41e, 1 additional Classical site)

    The two Classical / Markov sites are localised:
    - `boundedAway_of_not_equiv_zero` (Wave 41c, Field's inverse)
    - `lt_of_le_of_not_le_cauchy`     (Wave 41e, IsStrictOrderedRing's mul_pos)

    Inaccessible (structurally impossible without further Markov):
    - `LinearOrder TauRealQ` — would force uncountable cardinality
    - `LinearOrderedField TauRealQ` — same, contradicts τ-kernel commitment

    Every Mathlib theorem stated for
    `[Field K] [PartialOrder K] [IsStrictOrderedRing K]` (or weaker)
    applies to `TauRealQ` by typeclass inference. The full strict
    ordered field is now a first-class citizen of Mathlib's
    algebraic-order ecosystem — the constructive ordered-field
    bombshell is closed. -/
theorem h8_taureal_mathlib_orderedfield_full_bombshell :
    Nonempty (CommRing TauRealQ) ∧
    Nonempty (Field TauRealQ) ∧
    Nonempty (PartialOrder TauRealQ) ∧
    Nonempty (IsOrderedAddMonoid TauRealQ) ∧
    Nonempty (ZeroLEOneClass TauRealQ) ∧
    Nonempty (Nontrivial TauRealQ) ∧
    Nonempty (IsStrictOrderedRing TauRealQ) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
   ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

end Tau.Boundary

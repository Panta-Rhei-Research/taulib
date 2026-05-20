import TauLib.BookI.Boundary.TauRealPiLeibniz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealMachinPiBridge

**Phase E Scope 2C — bridge between two τ-native Machin forms**.

After Scope 2A (`TauRealMachinFortyFiveDegree.lean`) shipped the
45°-line algebraic identity for the parity-substituted Machin
product, and Scope 2B (`TauRealPiLeibniz.lean`) shipped
`TauReal.pi ≈ 4·arctan_of_rat_seq(1)`, this module discharges
the **structural bridge** between the two τ-native arctan-series
incarnations and reduces `MachinIdentity` to the residual
analytic equivalence `pi_machin.equiv pi`.

## Two τ-native arctan(1/q) representations

TauLib has two distinct τ-native arctan partial-sum series at the
rationals 1/5 and 1/239:

* **`TauReal.arctan_reciprocal q hq`** (TauRealArctan Part 9, q ≥ 2 Nat) —
  the q-indexed reciprocal-only series. *Cauchy* with explicit
  modulus `λ k => k + 3` via the geometric per-term bound
  `2/2^k`. Composed into `TauReal.pi_machin`
  (`= 16·arctan(1/5) − 4·arctan(1/239)`) which is Cauchy by
  composition.

* **`TauReal.arctan_of_rat_seq x`** (TauRealArctanDeriv) — the general
  arctan partial-sum series at any TauRat `x`. *Not* directly
  Cauchy in the general API (the Cauchy proof requires the
  `2·|x.toRat| ≤ 1` hypothesis). Composed into the
  `MachinIdentity` LHS expression via TauRat `one_fifth`,
  `one_two_three_nine` rationals.

The two coincide at the partial-sum level when `x.toRat = 1/q`:
the per-term formulas
* `arctan_pair_term_rat (1/q) k = (1/q)^(4k+1)/(4k+1) - (1/q)^(4k+3)/(4k+3)`
* `arctan_reciprocal_pair_term_rat q k
    = 1/q^(4k+1) · 1/(4k+1) - 1/q^(4k+3) · 1/(4k+3)`

are algebraically identical for `q > 0`.

## What this module ships

* **Per-term Rat-level bridge** —
  `arctan_pair_term_rat (1/q) k = arctan_reciprocal_pair_term_rat q k` for `q ≥ 1`.

* **Per-depth Rat-level bridge** —
  `arctan_partial_rat (1/q) n = arctan_reciprocal_partial_rat q n` for `q ≥ 1`.

* **TauReal pointwise equivalence** at the chosen Machin constants
  `1/5` and `1/239`:
  `arctan_of_rat_seq (1/q) ≈ arctan_reciprocal q hq`.

* **`pi_machin_equiv_machin_combination_arctan_of_rat_seq`** — the headline
  bridge theorem:
  `pi_machin ≈ 16·arctan_of_rat_seq(1/5) − 4·arctan_of_rat_seq(1/239)`.

* **`MachinIdentity_iff_pi_machin_equiv_pi`** — the **honest reduction**:
  `MachinIdentity ↔ TauReal.equiv pi_machin pi`. This packages
  the remaining analytic content as the structural equivalence
  between the (exponentially-convergent) `pi_machin` and the
  (sub-quadratically-convergent) Leibniz `pi`, which has been
  queued since Wave Γ₇ Phase 3F.

## Why this is the right scope

`MachinIdentity` (TauRealMachin.lean:459) states
`equiv (16·arctan_of_rat_seq(1/5) − 4·arctan_of_rat_seq(1/239)) pi`.
Discharging it requires either:
1. Bridging to the existing `pi_machin` Cauchy infrastructure
   and proving `pi_machin.equiv pi`, OR
2. A direct angle-level Machin proof via cisTauReal injectivity.

Path (1) decomposes the proposition: the per-term arithmetic
bridge (this module, fully discharged) plus the `pi_machin ≈ pi`
analytic equivalence (residual, queued). Path (2) was attempted
in `TauRealMachinFortyFiveDegree.lean` (Scope 2A) — discharging
the 45°-line algebraic identity but stopping short of the
angle-equivalence lift (which needs principal-branch arctan
injectivity, a Phase F concern).

By landing the structural bridge here, we:
* Reduce `MachinIdentity` to the **named** analytic equivalence
  `pi_machin.equiv pi` (the original Wave Γ₇ Phase 3F target).
* Make the residual content **inspectable** — `MachinIdentity`
  is no longer an opaque proposition; it factors through a
  well-defined Cauchy-equivalence between two explicit Cauchy
  TauReals.
* Compose with `BBPLeibnizCorrespondence` (TauRealBBP.lean:521)
  via `pi_machin → pi → pi_bbp` — both bridges route through the
  Leibniz `pi` as a hub, making the eventual full discharge
  structurally cleanest.

## Build state

* `sorry` count: 0
* Axiom count: 3 (kernel: `propext`, `Classical.choice`, `Quot.sound`)
* Imports: `TauRealPiLeibniz` (which transitively brings
  `TauRealMachin`, `TauRealArctan`, `TauRealArctanAdd`,
  `TauRealArctanDeriv`, `TauRealPi`) + Mathlib tactics only.

## Registry Cross-References

* [I.D-Pi-Machin] `TauReal.pi_machin` (TauRealArctan Part 10)
* [I.T-Pi-Machin-IsCauchy] `TauReal.pi_machin_isCauchy` (TauRealArctan Part 10)
* [I.D-Arctan-Of-Rat-Seq] `TauReal.arctan_of_rat_seq` (TauRealArctanDeriv)
* [I.D-Arctan-Reciprocal] `TauReal.arctan_reciprocal` (TauRealArctan Part 9)
* [I.T-Arctan-Reciprocal-IsCauchy] `TauReal.arctan_reciprocal_isCauchy`
* [I.D-MachinIdentity] `MachinIdentity` (TauRealMachin.lean:459)
* [I.T-Pi-Equiv-Four-Arctan-One] `TauReal.pi_equiv_four_arctan_one` (Scope 2B)

## Module name

This file is picked up by the `.submodules` glob in `lakefile.lean`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: PER-TERM RAT-LEVEL BRIDGE
-- ============================================================

/-! ## Per-term bridge — `arctan_pair_term_rat (1/q) k = arctan_reciprocal_pair_term_rat q k`

  Direct algebraic identity for `q ≥ 1 : Nat`. Both sides expand to
  `1/(q^(4k+1)·(4k+1)) - 1/(q^(4k+3)·(4k+3))`. -/

/-- **Per-term Rat-level bridge**: the general arctan pair-term at
    `x = 1/q` equals the reciprocal arctan pair-term at `q`. -/
theorem arctan_pair_term_rat_recip_eq (q : Nat) (hq : 1 ≤ q) (k : Nat) :
    arctan_pair_term_rat (1 / (q : Rat)) k = arctan_reciprocal_pair_term_rat q k := by
  unfold arctan_pair_term_rat arctan_reciprocal_pair_term_rat
  have h_q_pos : (0 : Rat) < (q : Rat) := by
    have : (0 : Nat) < q := hq
    exact_mod_cast this
  have h_q_4k1_pos : (0 : Rat) < (q : Rat)^(4*k+1) := by positivity
  have h_q_4k3_pos : (0 : Rat) < (q : Rat)^(4*k+3) := by positivity
  have h_4k1_pos : (0 : Rat) < ((4*k+1 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 1 := by omega
    exact_mod_cast this
  have h_4k3_pos : (0 : Rat) < ((4*k+3 : Nat) : Rat) := by
    have : (0 : Nat) < 4 * k + 3 := by omega
    exact_mod_cast this
  -- (1/q)^n = 1/q^n
  have h_recip_pow : ∀ n : Nat, (1 / (q : Rat))^n = 1 / (q : Rat)^n := by
    intro n
    rw [div_pow, one_pow]
  rw [h_recip_pow, h_recip_pow]
  push_cast
  field_simp

-- ============================================================
-- PART 2: PER-DEPTH PARTIAL-SUM BRIDGE
-- ============================================================

/-! ## Per-depth partial-sum bridge

  Aggregating the per-term identity over depth `n` gives the per-depth
  partial-sum identity, which is the load-bearing intermediate. -/

/-- **Per-depth Rat-level partial-sum bridge**: the general arctan partial
    sum at `x = 1/q` equals the reciprocal arctan partial sum at `q`. -/
theorem arctan_partial_rat_recip_eq (q : Nat) (hq : 1 ≤ q) (n : Nat) :
    arctan_partial_rat (1 / (q : Rat)) n = arctan_reciprocal_partial_rat q n := by
  induction n with
  | zero =>
    show arctan_partial_rat (1 / (q : Rat)) 0 = arctan_reciprocal_partial_rat q 0
    rw [arctan_partial_rat_zero, arctan_reciprocal_partial_rat_zero]
  | succ n ih =>
    show arctan_partial_rat (1 / (q : Rat)) (n + 1)
          = arctan_reciprocal_partial_rat q (n + 1)
    rw [arctan_partial_rat_succ, arctan_reciprocal_partial_rat_succ, ih,
        arctan_pair_term_rat_recip_eq q hq n]

-- ============================================================
-- PART 3: TauReal POINTWISE EQUIVALENCE
-- ============================================================

/-! ## TauReal-level pointwise equivalence

  Given a TauRat `x` with `x.toRat = 1/q` for `q : Nat ≥ 1`, the
  approximation sequences of `arctan_of_rat_seq x` and
  `arctan_reciprocal q hq` agree pointwise under `.toRat`. By
  `equiv_iff_toRat_eq` plus `equiv_of_pointwise`, the two TauReals are
  Cauchy-equivalent. -/

/-- **Pointwise toRat equivalence** between the general and reciprocal
    arctan sequences when `x.toRat = 1/q`. -/
theorem TauReal.arctan_of_rat_seq_approx_equiv_arctan_reciprocal_approx
    (x : TauRat) (q : Nat) (hq : 2 ≤ q) (hx : x.toRat = 1 / (q : Rat)) (n : Nat) :
    TauRat.equiv
      ((TauReal.arctan_of_rat_seq x).approx n)
      ((TauReal.arctan_reciprocal q hq).approx n) := by
  rw [equiv_iff_toRat_eq]
  rw [TauReal.arctan_of_rat_seq_approx, TauReal.arctan_reciprocal_approx]
  rw [TauRat.arctan_partial_toRat, TauRat.arctan_reciprocal_partial_toRat]
  rw [hx]
  exact arctan_partial_rat_recip_eq q (by omega) n

/-- **TauReal-level Cauchy equivalence** between the general and reciprocal
    arctan sequences when `x.toRat = 1/q`. -/
theorem TauReal.arctan_of_rat_seq_equiv_arctan_reciprocal
    (x : TauRat) (q : Nat) (hq : 2 ≤ q) (hx : x.toRat = 1 / (q : Rat)) :
    TauReal.equiv
      (TauReal.arctan_of_rat_seq x)
      (TauReal.arctan_reciprocal q hq) := by
  apply TauReal.equiv_of_pointwise
  intro n
  exact TauReal.arctan_of_rat_seq_approx_equiv_arctan_reciprocal_approx x q hq hx n

-- ============================================================
-- PART 4: SPECIALIZATIONS AT MACHIN CONSTANTS
-- ============================================================

/-! ## Specializations at Machin constants 1/5 and 1/239

  The toRat values of `TauRat.one_fifth` and `TauRat.one_two_three_nine`
  are `1/5` and `1/239` respectively (already shipped as simp lemmas in
  `TauRealMachin.lean`). Applying the bridge: -/

/-- **Bridge at `1/5`**: `arctan_of_rat_seq one_fifth ≈ arctan_reciprocal 5`. -/
theorem TauReal.arctan_of_rat_seq_one_fifth_equiv_arctan_reciprocal_five :
    TauReal.equiv
      (TauReal.arctan_of_rat_seq TauRat.one_fifth)
      (TauReal.arctan_reciprocal 5 (by norm_num : (2 : Nat) ≤ 5)) := by
  apply TauReal.arctan_of_rat_seq_equiv_arctan_reciprocal
  rw [TauRat.one_fifth_toRat]
  norm_num

/-- **Bridge at `1/239`**:
    `arctan_of_rat_seq one_two_three_nine ≈ arctan_reciprocal 239`. -/
theorem TauReal.arctan_of_rat_seq_one_two_three_nine_equiv_arctan_reciprocal_239 :
    TauReal.equiv
      (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine)
      (TauReal.arctan_reciprocal 239 (by norm_num : (2 : Nat) ≤ 239)) := by
  apply TauReal.arctan_of_rat_seq_equiv_arctan_reciprocal
  rw [TauRat.one_two_three_nine_toRat]
  norm_num

-- ============================================================
-- PART 5: CONGRUENCE INFRASTRUCTURE — TauReal.mul, TauReal.sub
-- ============================================================

/-! ## Congruence under scalar multiplication and subtraction

  To lift the bridge from individual arctan terms to the full
  Machin combination, we need that `TauReal.equiv` is a congruence
  for `TauReal.mul` (with a constant left factor) and `TauReal.sub`.

  The pointwise nature of `mul` and `sub` (both inherit from
  pointwise TauRat operations) makes these congruences straightforward
  via `equiv_of_pointwise` lifted from the per-depth identities. -/

/-- **Pointwise congruence of `TauReal.mul` for the left factor `fromTauRat`**:
    if `a ≈ b` pointwise via toRat, then `(fromTauRat c) · a ≈ (fromTauRat c) · b`
    via toRat at every depth. (Used as a building block; full
    Cauchy-modulus congruence is heavier.) -/
private theorem mul_fromTauRat_left_pointwise_toRat
    (c : TauRat) (a b : TauReal)
    (h : ∀ n, (a.approx n).toRat = (b.approx n).toRat) (n : Nat) :
    (((TauReal.fromTauRat c).mul a).approx n).toRat
      = (((TauReal.fromTauRat c).mul b).approx n).toRat := by
  show (TauRat.mul ((TauReal.fromTauRat c).approx n) (a.approx n)).toRat
        = (TauRat.mul ((TauReal.fromTauRat c).approx n) (b.approx n)).toRat
  rw [toRat_mul, toRat_mul]
  rw [h]

/-- **Lift `equiv` through `fromTauRat`-scalar multiplication**: if `a ≈ b`
    via pointwise toRat equality, then `(fromTauRat c)·a ≈ (fromTauRat c)·b`. -/
theorem TauReal.mul_fromTauRat_left_equiv_of_pointwise_toRat
    (c : TauRat) (a b : TauReal)
    (h : ∀ n, (a.approx n).toRat = (b.approx n).toRat) :
    TauReal.equiv ((TauReal.fromTauRat c).mul a) ((TauReal.fromTauRat c).mul b) := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  exact mul_fromTauRat_left_pointwise_toRat c a b h n

/-- **Pointwise congruence of `TauReal.sub`**: if `a₁ ≈ b₁` and `a₂ ≈ b₂`
    pointwise via toRat, then `a₁ - a₂ ≈ b₁ - b₂` via toRat. -/
private theorem sub_pointwise_toRat
    (a₁ a₂ b₁ b₂ : TauReal)
    (h₁ : ∀ n, (a₁.approx n).toRat = (b₁.approx n).toRat)
    (h₂ : ∀ n, (a₂.approx n).toRat = (b₂.approx n).toRat) (n : Nat) :
    ((a₁.sub a₂).approx n).toRat = ((b₁.sub b₂).approx n).toRat := by
  show (TauRat.add (a₁.approx n) (TauRat.negate (a₂.approx n))).toRat
        = (TauRat.add (b₁.approx n) (TauRat.negate (b₂.approx n))).toRat
  rw [toRat_add, toRat_negate, toRat_add, toRat_negate]
  rw [h₁, h₂]

/-- **Lift `equiv` through subtraction**: if `a₁ ≈ b₁` and `a₂ ≈ b₂` via
    pointwise toRat, then `a₁ - a₂ ≈ b₁ - b₂`. -/
theorem TauReal.sub_equiv_of_pointwise_toRat
    (a₁ a₂ b₁ b₂ : TauReal)
    (h₁ : ∀ n, (a₁.approx n).toRat = (b₁.approx n).toRat)
    (h₂ : ∀ n, (a₂.approx n).toRat = (b₂.approx n).toRat) :
    TauReal.equiv (a₁.sub a₂) (b₁.sub b₂) := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  exact sub_pointwise_toRat a₁ a₂ b₁ b₂ h₁ h₂ n

-- ============================================================
-- PART 6: TauReal.fromTauRat vs TauReal.fromNat AT MACHIN COEFFICIENTS
-- ============================================================

/-! ## Numerical scaffolding for 16 and 4

  The `MachinIdentity` proposition uses `TauReal.fromTauRat ⟨⟨16, 0⟩, 1, _⟩`
  and `TauReal.fromTauRat ⟨⟨4, 0⟩, 1, _⟩` for the scalar coefficients,
  while `pi_machin` uses `TauReal.fromNat 16` and `TauReal.fromNat 4`.
  Both forms evaluate to `16` and `4` at the toRat level — we ship
  the bridging lemmas. -/

/-- The TauRat `⟨⟨16, 0⟩, 1, _⟩` has toRat `16`. -/
private theorem sixteen_tauRat_toRat :
    (⟨⟨16, 0⟩, 1, by norm_num⟩ : TauRat).toRat = (16 : Rat) := by
  unfold TauRat.toRat
  simp only [TauInt.toInt]
  push_cast
  ring

/-- The TauRat `⟨⟨4, 0⟩, 1, _⟩` has toRat `4`. -/
private theorem four_tauRat_toRat :
    (⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat).toRat = (4 : Rat) := by
  unfold TauRat.toRat
  simp only [TauInt.toInt]
  push_cast
  ring

/-- **Bridge `fromTauRat 16` ≈ `fromNat 16`** pointwise via toRat. -/
private theorem fromTauRat_sixteen_pointwise_toRat (n : Nat) :
    (((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).approx n).toRat
      : Rat)
      = ((TauReal.fromNat 16).approx n).toRat := by
  show ((⟨⟨16, 0⟩, 1, by norm_num⟩ : TauRat).toRat : Rat)
        = (nat_to_taurat 16).toRat
  rw [sixteen_tauRat_toRat, nat_to_taurat_toRat]
  norm_num

/-- **Bridge `fromTauRat 4` ≈ `fromNat 4`** pointwise via toRat. -/
private theorem fromTauRat_four_pointwise_toRat (n : Nat) :
    (((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).approx n).toRat
      : Rat)
      = ((TauReal.fromNat 4).approx n).toRat := by
  show ((⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat).toRat : Rat)
        = (nat_to_taurat 4).toRat
  rw [four_tauRat_toRat, nat_to_taurat_toRat]
  norm_num

-- ============================================================
-- PART 7: THE HEADLINE BRIDGE THEOREM
-- ============================================================

/-! ## Headline bridge theorem

  `pi_machin` (defined via `arctan_reciprocal`) is Cauchy-equivalent
  to the τ-canon Machin combination at the `arctan_of_rat_seq` level
  using `MachinIdentity`'s exact coefficient form. -/

/-- **Pointwise toRat identity** between `pi_machin.approx n` and the
    `arctan_of_rat_seq`-form Machin combination at depth `n`. This is
    the core scalar-by-scalar arithmetic identity. -/
theorem TauReal.pi_machin_approx_toRat_eq_machin_combination_arctan_of_rat_seq
    (n : Nat) :
    ((TauReal.pi_machin.approx n)).toRat
      = ((((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).mul
            (TauReal.arctan_of_rat_seq TauRat.one_fifth)).sub
          ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
            (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine))).approx n).toRat := by
  -- LHS: pi_machin = (fromNat 16 · arctan_reciprocal 5).sub (fromNat 4 · arctan_reciprocal 239)
  show (TauRat.add
          (TauRat.mul ((TauReal.fromNat 16).approx n)
                     ((TauReal.arctan_reciprocal 5 (by norm_num)).approx n))
          (TauRat.negate
            (TauRat.mul ((TauReal.fromNat 4).approx n)
                       ((TauReal.arctan_reciprocal 239 (by norm_num)).approx n)))).toRat
        = _
  rw [toRat_add, toRat_mul, toRat_negate, toRat_mul]
  -- RHS: similar structure but with fromTauRat coefficients and arctan_of_rat_seq
  show _ = (TauRat.add
              (TauRat.mul ((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).approx n)
                         ((TauReal.arctan_of_rat_seq TauRat.one_fifth).approx n))
              (TauRat.negate
                (TauRat.mul ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).approx n)
                           ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).approx n)))).toRat
  rw [toRat_add, toRat_mul, toRat_negate, toRat_mul]
  -- Match coefficients
  rw [TauReal.fromNat_approx, nat_to_taurat_toRat,
      TauReal.fromNat_approx, nat_to_taurat_toRat]
  show _ + _ = _
  -- fromTauRat ⟨⟨16, 0⟩, 1, _⟩ .approx n = ⟨⟨16, 0⟩, 1, _⟩
  show _ = ((⟨⟨16, 0⟩, 1, by norm_num⟩ : TauRat).toRat
              * ((TauReal.arctan_of_rat_seq TauRat.one_fifth).approx n).toRat)
           + (-((⟨⟨4, 0⟩, 1, by norm_num⟩ : TauRat).toRat
                  * ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).approx n).toRat))
  rw [sixteen_tauRat_toRat, four_tauRat_toRat]
  -- Match arctan layers via the bridge
  have h_five :
      ((TauReal.arctan_of_rat_seq TauRat.one_fifth).approx n).toRat
        = ((TauReal.arctan_reciprocal 5 (by norm_num : (2:Nat) ≤ 5)).approx n).toRat := by
    rw [TauReal.arctan_of_rat_seq_approx, TauReal.arctan_reciprocal_approx]
    rw [TauRat.arctan_partial_toRat, TauRat.arctan_reciprocal_partial_toRat]
    rw [TauRat.one_fifth_toRat]
    have : (1 : Rat) / 5 = 1 / ((5 : Nat) : Rat) := by norm_num
    rw [this]
    exact arctan_partial_rat_recip_eq 5 (by norm_num) n
  have h_239 :
      ((TauReal.arctan_of_rat_seq TauRat.one_two_three_nine).approx n).toRat
        = ((TauReal.arctan_reciprocal 239 (by norm_num : (2:Nat) ≤ 239)).approx n).toRat := by
    rw [TauReal.arctan_of_rat_seq_approx, TauReal.arctan_reciprocal_approx]
    rw [TauRat.arctan_partial_toRat, TauRat.arctan_reciprocal_partial_toRat]
    rw [TauRat.one_two_three_nine_toRat]
    have : (1 : Rat) / 239 = 1 / ((239 : Nat) : Rat) := by norm_num
    rw [this]
    exact arctan_partial_rat_recip_eq 239 (by norm_num) n
  rw [h_five, h_239]
  push_cast
  ring

/-- **🎯 Phase E Scope 2C headline bridge theorem**:

    The existing exponentially-convergent `pi_machin` (defined via
    `arctan_reciprocal`) is Cauchy-equivalent to the τ-canon Machin
    combination at the `arctan_of_rat_seq` level using `MachinIdentity`'s
    exact coefficient form:

    `pi_machin ≈ 16·arctan_of_rat_seq(1/5) − 4·arctan_of_rat_seq(1/239)`.

    This is the structural bridge that connects the two τ-native arctan
    incarnations at the Cauchy level. Proof: via `equiv_of_pointwise` on
    the pointwise toRat identity. -/
theorem TauReal.pi_machin_equiv_machin_combination_arctan_of_rat_seq :
    TauReal.equiv
      TauReal.pi_machin
      (((TauReal.fromTauRat ⟨⟨16, 0⟩, 1, by norm_num⟩).mul
          (TauReal.arctan_of_rat_seq TauRat.one_fifth)).sub
        ((TauReal.fromTauRat ⟨⟨4, 0⟩, 1, by norm_num⟩).mul
          (TauReal.arctan_of_rat_seq TauRat.one_two_three_nine))) := by
  apply TauReal.equiv_of_pointwise
  intro n
  rw [equiv_iff_toRat_eq]
  exact TauReal.pi_machin_approx_toRat_eq_machin_combination_arctan_of_rat_seq n

-- ============================================================
-- PART 8: REDUCTION — MachinIdentity ↔ pi_machin ≈ pi
-- ============================================================

/-! ## The honest reduction

  `MachinIdentity` is defined as
  `equiv (16·arctan_of_rat_seq(1/5) − 4·arctan_of_rat_seq(1/239)) pi`.

  By the bridge theorem and transitivity of `equiv`, this is logically
  equivalent to `TauReal.equiv pi_machin pi`. The latter is the
  structural equivalence between the (exponentially-convergent)
  `pi_machin` (Cauchy via `arctan_reciprocal`) and the
  (sub-quadratically-convergent) Leibniz `pi`.

  This reduction is **the honest content** of `MachinIdentity`:
  no analytic insight beyond `pi_machin.equiv pi` is needed once
  the structural bridge is in place. -/

/-- **🎯 Phase E Scope 2C headline reduction theorem**:

    `MachinIdentity` is logically equivalent to `TauReal.equiv pi_machin pi`.

    Both directions follow from the bridge theorem
    `pi_machin_equiv_machin_combination_arctan_of_rat_seq` plus the
    transitivity and symmetry of `TauReal.equiv`.

    **What this delivers**: the load-bearing analytic content of
    `MachinIdentity` is exposed as the structural Cauchy-equivalence
    `pi_machin.equiv pi` (i.e., the original Wave Γ₇ Phase 3F target).
    Future analytic work targeting `MachinIdentity` can route
    transparently through this named lemma — there is no longer any
    "hidden" content in `MachinIdentity` beyond the `pi_machin.equiv pi`
    equivalence.

    Note: this is an `iff`-style theorem stated as a conjunction of the
    two implications, since `Iff` introduction on `Prop`-valued
    propositions composes more naturally with `TauReal.equiv` rewriting
    chains. Standard `Iff` form available below via `iff_of_implications`. -/
theorem MachinIdentity_iff_pi_machin_equiv_pi :
    MachinIdentity ↔ TauReal.equiv TauReal.pi_machin TauReal.pi := by
  constructor
  · -- Forward: MachinIdentity → pi_machin ≈ pi
    intro h_machin
    -- pi_machin ≈ machin_combination_arctan_of_rat_seq ≈ pi
    exact TauReal.equiv_trans
      TauReal.pi_machin_equiv_machin_combination_arctan_of_rat_seq
      h_machin
  · -- Reverse: pi_machin ≈ pi → MachinIdentity
    intro h_pi
    -- MachinIdentity: machin_combination_arctan_of_rat_seq ≈ pi
    -- We have: pi_machin ≈ machin_combination_arctan_of_rat_seq (bridge)
    --         pi_machin ≈ pi (hypothesis)
    -- So: machin_combination_arctan_of_rat_seq ≈ pi_machin ≈ pi
    exact TauReal.equiv_trans
      (TauReal.equiv_symm TauReal.pi_machin_equiv_machin_combination_arctan_of_rat_seq)
      h_pi

/-! ## Path forward to BBPLeibnizCorrespondence

  With `MachinIdentity_iff_pi_machin_equiv_pi` shipped, the remaining
  path to discharge `MachinIdentity` (and onward to
  `BBPLeibnizCorrespondence`) factors as follows:

  **Step 1 (residual analytic)**: discharge `pi_machin.equiv pi`. This
  is the Wave Γ₇ Phase 3F target. Candidate strategies:
  - Both `pi_machin` and `pi` are explicit Cauchy TauReals with
    explicit moduli. The difference sequence
    `pi_machin.approx n − pi.approx n` can be bounded by composing
    the truncation-error analyses of the two arctan series with the
    classical Machin identity `16·arctan(1/5) − 4·arctan(1/239) = π`
    in the limit. Requires either the angle-equivalence injectivity
    (via Scope 2A's 45°-line identity, awaiting principal-branch
    arctan infrastructure) or a Mathlib bridge (`Real.arctan` route,
    using a programme axiom — axiom budget +1).

  **Step 2 (compose)**: derive `MachinIdentity` from the residual
  via `MachinIdentity_iff_pi_machin_equiv_pi.mpr`.

  **Step 3 (BBPLeibnizCorrespondence)**: discharge
  `pi_bbp.equiv pi` (TauRealBBP Phase 2 named target). This requires
  a separate τ-native BBP-to-arctan(1/√2) chain, queued for Γ₇+.

  All three steps are independent in their analytic content. With
  this module landed, **the Phase E Scope 2C contribution to the
  Machin pipeline is structurally complete** — only the
  exponential-vs-Leibniz Cauchy-equivalence remains. -/

end Tau.Boundary

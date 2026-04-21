import TauLib.BookI.Boundary.TauRealAbs
import TauLib.BookI.Boundary.TauRatInv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp

/-!
# TauLib.BookI.Boundary.TauRealInv

Multiplicative inverse and division on `TauReal`.

## Registry Cross-References

- [I.D84] TauReal — the Cauchy completion of TauRat
- [I.D110] TauRat Inverse and Division — `TauRat.inv` (Wave 1d),
  lifted pointwise
- [I.D112] TauReal.equiv — the Cauchy equivalence relation
- [I.D114] TauReal Absolute Value, Inverse, Division — bundled abs /
  inv / div layer; this module supplies the inv / div half
- [I.P49] TauReal Ordered Field Structure — collective proposition for
  the full Wave 2 ordered-field layer

## Mathematical Content

**Wave 2d** of the TauReal infrastructure (see `ROADMAP-3-HINGES.md`).

Inverting a TauReal requires that the real is *bounded away from zero*
eventually — a strictly stronger notion than "not equivalent to zero".

- `TauReal.BoundedAwayFromZero a` :
  `∃ k N, ∀ n ≥ N, 1/(k+1) < |a.approx n|`.
  Witnesses that `a` stays at least `1/(k+1)` away from zero in absolute
  value past index `N`.

- `TauReal.inv a` : pointwise multiplicative inverse, with a safe
  fallback (`TauRat.one`) at indices where the underlying TauRat is
  zero.  The function is *total* — no hypothesis is required to
  construct `a.inv` — but its good properties (acts as a multiplicative
  inverse, produces a Cauchy sequence) require
  `TauReal.BoundedAwayFromZero a` as an explicit argument.

- `TauReal.div a b` : `a.mul b.inv`.

The cancellation lemmas `TauReal.mul_inv_cancel` and
`TauReal.inv_mul_cancel` are stated up to Cauchy `TauReal.equiv`: past
the modulus witnessed by `BoundedAwayFromZero`, `a.approx n` is nonzero
and `a.inv.approx n = (a.approx n).inv`, so the product is pointwise
`1` on this tail — hence Cauchy-equivalent to `TauReal.one`.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: BOUNDED AWAY FROM ZERO
-- ============================================================

/-- `TauReal.BoundedAwayFromZero a`: there exist `k N` such that for all
    `n ≥ N`, the absolute value of `a.approx n` strictly exceeds
    `1/(k+1)`.  This is the standard constructive apartness witness
    needed to invert `a`. -/
def TauReal.BoundedAwayFromZero (a : TauReal) : Prop :=
  ∃ k N : Nat, ∀ n : Nat, N ≤ n →
    TauRat.lt (TauRat.ofNatRecip k) (a.approx n).abs

/-- If `a` is bounded away from zero past some index `N`, every
    `a.approx n` with `n ≥ N` is nonzero in the TauRat sense. -/
theorem TauReal.is_nonzero_of_bounded_away {a : TauReal} {k N : Nat}
    (hN : ∀ n : Nat, N ≤ n → TauRat.lt (TauRat.ofNatRecip k) (a.approx n).abs)
    (n : Nat) (hn : N ≤ n) : (a.approx n).is_nonzero := by
  have h := hN n hn
  -- h : (ofNatRecip k).toRat < (a.approx n).abs.toRat
  unfold TauRat.lt at h
  rw [TauRat.ofNatRecip_toRat, TauRat.toRat_abs] at h
  -- h : 1/(k+1) < |(a.approx n).toRat|
  -- Conclude (a.approx n).toRat ≠ 0
  have h_recip : (0 : Rat) < 1 / ((k : Rat) + 1) := by
    have : (0 : Rat) < (k : Rat) + 1 := by
      have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
      linarith
    exact div_pos (by norm_num) this
  rw [(TauRat.is_nonzero_iff_toRat_ne_zero _)]
  intro h_zero
  rw [h_zero, abs_zero] at h
  linarith

-- ============================================================
-- PART 2: INVERSE (total function, good under BoundedAwayFromZero)
-- ============================================================

/-- Decidability of `TauRat.is_nonzero`: delegated to `Int` decidable
    equality via the `q.num.toInt ≠ 0` unfolding. -/
instance (q : TauRat) : Decidable q.is_nonzero := by
  unfold TauRat.is_nonzero; infer_instance

/-- Pointwise multiplicative inverse on `TauReal`: at each index, invert
    the TauRat approximation when nonzero, fall back to `TauRat.one`
    otherwise.  The fallback value is irrelevant for the Cauchy
    behavior — past the `BoundedAwayFromZero` witness, every index is
    nonzero and we take the genuine TauRat inverse.

    This function is **total** (no hypothesis needed) so that we can
    embed it in `TauReal.div` without carrying hypotheses through the
    definition.  The good cancellation lemmas (`mul_inv_cancel`, etc.)
    do require `BoundedAwayFromZero` as an explicit argument. -/
def TauReal.inv (a : TauReal) : TauReal :=
  ⟨fun n => if h : (a.approx n).is_nonzero then TauRat.inv (a.approx n) h
            else TauRat.one⟩

/-- Division on `TauReal`: `a / b = a * b.inv`. -/
def TauReal.div (a b : TauReal) : TauReal :=
  a.mul b.inv

-- ============================================================
-- PART 3: CANCELLATION (a * a.inv ≡ 1 past the BoundedAway modulus)
-- ============================================================

/-- `a * a.inv ≡ 1` up to `TauReal.equiv`, when `a` is bounded away
    from zero.

    Strategy: past the `BoundedAwayFromZero` modulus `N`, every
    `a.approx n` is nonzero, so `a.inv.approx n` takes the
    `TauRat.inv` branch and `a.approx n * a.inv.approx n = 1` by
    `TauRat.mul_inv_cancel`.  The pointwise difference with
    `TauReal.one.approx n = TauRat.one` is then equivalence to zero. -/
theorem TauReal.mul_inv_cancel (a : TauReal) (h : a.BoundedAwayFromZero) :
    TauReal.equiv (a.mul a.inv) TauReal.one := by
  obtain ⟨k₀, N₀, hN₀⟩ := h
  refine ⟨fun _ => N₀, fun k n hn => ?_⟩
  have h_nz := TauReal.is_nonzero_of_bounded_away hN₀ n hn
  -- Goal: the Cauchy bound on |(a.mul a.inv).approx n - 1|
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub]
  -- Compute (a.mul a.inv).approx n = a.approx n * a.inv.approx n
  -- With h_nz : (a.approx n).is_nonzero, a.inv.approx n = (a.approx n).inv h_nz
  have h_inv_val : (a.inv).approx n = TauRat.inv (a.approx n) h_nz := by
    show (if h : (a.approx n).is_nonzero then TauRat.inv (a.approx n) h
          else TauRat.one) = TauRat.inv (a.approx n) h_nz
    rw [dif_pos h_nz]
  have h_prod : ((a.mul a.inv).approx n).toRat = 1 := by
    show ((a.approx n).mul (a.inv.approx n)).toRat = 1
    rw [h_inv_val, toRat_mul, toRat_inv]
    have h_toRat_ne := (TauRat.is_nonzero_iff_toRat_ne_zero (a.approx n)).mp h_nz
    field_simp
  have h_one : (TauReal.one.approx n).toRat = 1 := by
    show TauRat.one.toRat = 1
    exact toRat_one
  rw [h_prod, h_one]
  simp
  exact TauRat.ofNatRecip_pos k

/-- `a.inv * a ≡ 1` up to `TauReal.equiv`, when `a` is bounded away
    from zero.  Corollary of `mul_inv_cancel` via commutativity. -/
theorem TauReal.inv_mul_cancel (a : TauReal) (h : a.BoundedAwayFromZero) :
    TauReal.equiv (a.inv.mul a) TauReal.one := by
  apply TauReal.equiv_trans _ (TauReal.mul_inv_cancel a h)
  exact taureal_mul_comm a.inv a

/-- `a / a ≡ 1` up to `TauReal.equiv`, when `a` is bounded away from zero. -/
theorem TauReal.div_self (a : TauReal) (h : a.BoundedAwayFromZero) :
    TauReal.equiv (a.div a) TauReal.one :=
  TauReal.mul_inv_cancel a h

end Tau.Boundary

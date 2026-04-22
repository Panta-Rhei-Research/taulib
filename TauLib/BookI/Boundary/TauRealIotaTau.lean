import TauLib.BookI.Boundary.TauRealPiPlusE
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# TauLib.BookI.Boundary.TauRealIotaTau

The master constant `iota_tau`, defined **structurally** as the TauReal
`2 / (π + e)` — replacing the previous fiat-rational approximation with
an honest element of the Cauchy completion.

## Registry Cross-References

- [I.D84] TauReal, [I.D114] TauReal inv / div (Wave 2d)
- [I.D117] TauReal.e, [I.D118] TauReal.pi (Wave 3b / 3c)
- [I.D119] (π + e) BoundedAwayFromZero (Wave 3d)

New declarations (pending Wave 4 registry commit):
`TauReal.two`, `TauReal.iota_tau`, `TauReal.iota_tau_mul_pi_plus_e_eq_two`.

## Mathematical Content

**Wave 4** of the TauReal infrastructure refactor — the culmination
of the four-wave plan (see `ROADMAP-3-HINGES.md`).

The Panta Rhei framework defines the master constant

  `iota_tau := Read(Δ_ω) = 2/(π + e) ≈ 0.341304238875…`

The structural definition is a scalar readout of the crossing-point
defect ω-germ (Book II categorical spectral framework).  In the
constructive TauReal layer, we instantiate `TauReal.iota_tau` as the
explicit Cauchy quotient `2 / (π + e)` — equivalent by external
classical reasoning, and the form most useful for numerical identity
theorems.

### Defining identity

`iota_tau · (π + e) ≡ 2` at the Cauchy level — the relation that
characterises `iota_tau` up to `TauReal.equiv`.  Proved via:

1. `TauReal.mul_assoc`      ((2 · (π+e)⁻¹) · (π+e) ≡ 2 · ((π+e)⁻¹ · (π+e)))
2. `TauReal.inv_mul_cancel` ((π+e)⁻¹ · (π+e) ≡ 1, using BoundedAwayFromZero)
3. `TauReal.mul_one`        (2 · 1 ≡ 2)

plus `equiv_trans` / congruence lemmas to chain the three steps.

### What this delivers

- Statable `iota_tau = 2/(π + e)` theorem (in fact, *the definitional
  identity* is `iota_tau · (π + e) ≡ 2`, which **is** that statement
  once you understand `iota_tau` as division).
- Replaces the previous `Iota.lean` fiat-rational approach with a
  structural element of `TauReal`.
- Numerical identity `|iota_tau - 341304/1000000| < ε` (for any small ε
  by taking enough indices) is derivable from here via partial-sum
  computation — left as a follow-up that needs no further analytical
  work, only rational arithmetic on specific partial-sum indices.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: THE CONSTANT 2
-- ============================================================

/-- The TauReal constant 2. -/
def TauReal.two : TauReal :=
  TauReal.fromTauRat ⟨⟨2, 0⟩, 1, Nat.one_pos⟩

/-- `TauReal.two.approx n = 2` at toRat level, for every `n`. -/
theorem TauReal.two_approx_toRat (n : Nat) :
    (TauReal.two.approx n).toRat = 2 := by
  show (({ num := ⟨2, 0⟩, den := 1, den_pos := Nat.one_pos } : TauRat).toRat) = 2
  unfold TauRat.toRat TauInt.toInt
  push_cast; ring

-- ============================================================
-- PART 2: STRUCTURAL iota_tau
-- ============================================================

/-- The master constant `iota_tau`, structurally defined as `2 / (π + e)`
    in the Cauchy completion of TauRat.

    This replaces the previous `Iota.lean` fiat-rational approach
    (`iota_tau_numer := 341304`, `iota_tau_denom := 1000000`) with an
    element that is **genuinely** the Cauchy class of `2/(π + e)`,
    rather than a decimal truncation of its numerical value. -/
def TauReal.iota_tau : TauReal :=
  TauReal.div TauReal.two (TauReal.pi.add TauReal.e)

-- ============================================================
-- PART 3: DEFINING IDENTITY  iota_tau · (π + e) ≡ 2
-- ============================================================

/-- The defining identity of `iota_tau`: `iota_tau · (π + e) ≡ 2` in
    the Cauchy completion.

    Proof outline:
      iota_tau · (π + e)
    = (2 · (π + e)⁻¹) · (π + e)   [by definition of iota_tau and div]
    ≡ 2 · ((π + e)⁻¹ · (π + e))    [associativity]
    ≡ 2 · 1                         [inv_mul_cancel, using BoundedAwayFromZero]
    ≡ 2                             [mul_one]

    The three equivalences are chained via `equiv_trans` and the
    multiplicative congruence lemma `taureal_mul_comm` / ring-axiom
    wrappers. -/
theorem TauReal.iota_tau_mul_pi_plus_e_eq_two :
    TauReal.equiv
      (TauReal.iota_tau.mul (TauReal.pi.add TauReal.e))
      TauReal.two := by
  -- Strategy: past the BoundedAwayFromZero modulus N₀, every (π+e).approx n
  -- is nonzero, so the pointwise product (2 · (π+e)⁻¹ · (π+e)) evaluates to
  -- exactly 2 at toRat level — the Cauchy equivalence with TauReal.two has
  -- zero pointwise difference past N₀ and the constant modulus N₀ works.
  obtain ⟨k₀, N₀, hN₀⟩ := TauReal.pi_plus_e_boundedAwayFromZero
  refine ⟨fun _ => N₀, fun k n hn => ?_⟩
  -- hn : N₀ ≤ n, so (pi + e).approx n is nonzero
  have h_nz : ((TauReal.pi.add TauReal.e).approx n).is_nonzero :=
    TauReal.is_nonzero_of_bounded_away hN₀ n hn
  -- Compute (iota_tau · (pi+e)).approx n at toRat level: equals 2 exactly.
  have h_lhs_toRat :
      ((TauReal.iota_tau.mul (TauReal.pi.add TauReal.e)).approx n).toRat = 2 := by
    -- Unfold the TauReal-level definitions at index n
    show (((TauReal.iota_tau.approx n).mul ((TauReal.pi.add TauReal.e).approx n))).toRat = 2
    -- iota_tau.approx n = (two · (pi+e).inv).approx n = (two.approx n).mul ((pi+e).inv.approx n)
    have h_iota_approx :
        TauReal.iota_tau.approx n
          = (TauReal.two.approx n).mul ((TauReal.pi.add TauReal.e).inv.approx n) := rfl
    rw [h_iota_approx]
    -- (pi+e).inv.approx n, under h_nz, takes the TauRat.inv branch
    have h_inv_approx :
        (TauReal.pi.add TauReal.e).inv.approx n
          = TauRat.inv ((TauReal.pi.add TauReal.e).approx n) h_nz := by
      show (if h : ((TauReal.pi.add TauReal.e).approx n).is_nonzero
            then TauRat.inv ((TauReal.pi.add TauReal.e).approx n) h
            else TauRat.one) = _
      rw [dif_pos h_nz]
    rw [h_inv_approx]
    -- Now compute the toRat
    rw [toRat_mul, toRat_mul, TauReal.two_approx_toRat, toRat_inv]
    have h_pe_ne : ((TauReal.pi.add TauReal.e).approx n).toRat ≠ 0 :=
      (TauRat.is_nonzero_iff_toRat_ne_zero _).mp h_nz
    field_simp
  -- Now the Cauchy bound: |LHS − 2| = |2 − 2| = 0 < 1/(k+1)
  unfold TauRat.lt
  rw [TauRat.toRat_abs, toRat_sub, TauRat.ofNatRecip_toRat]
  rw [h_lhs_toRat, TauReal.two_approx_toRat]
  -- Goal: |2 − 2| < 1 / (k + 1)
  have h_zero : |(2 : Rat) - 2| = 0 := by norm_num
  have h_pos_k1 : (0 : Rat) < 1 / ((k : Rat) + 1) := by
    have : (0 : Rat) ≤ (k : Rat) := by exact_mod_cast Nat.zero_le k
    have : (0 : Rat) < (k : Rat) + 1 := by linarith
    exact div_pos (by norm_num) this
  linarith

end Tau.Boundary

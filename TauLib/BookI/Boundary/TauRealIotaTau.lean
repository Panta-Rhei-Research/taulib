import TauLib.BookI.Boundary.TauRealPiPlusE
import TauLib.BookI.Boundary.Bridge.TauRealQuotient
import TauLib.BookI.Boundary.Bridge.TauRealQuotientField
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

- [I.D84]    TauReal, [I.D114] TauReal inv / div (Wave 2d)
- [I.D117]   TauReal.e, [I.D118] TauReal.pi (Wave 3b / 3c)
- [I.D119]   (π + e) BoundedAwayFromZero (Wave 3d)
- [I.D-IotaTau-Structural]   `TauReal.iota_tau` (Wave 4 — this module)
- [I.T-IotaTau-DefiningId]   `iota_tau · (π + e) ≡ 2` (Wave 4 — this module)
- [I.D-IotaTau-Fiat-TauRat]  `TauRat.iota_tau_fiat = 341304/1000000`
                              (Phase 0 / B1.0b — this module, PART 4)
- [I.T-IotaTau-IsCauchy]     `TauReal.iota_tau.IsCauchy` — asymptotic
                              bridge (Phase 0 / B1.0b — this module, PART 5)
- [I.T-IotaTau-Numerical-K50] `|iota_tau.approx 50 − 341304/1000000| < 1/1000`
                              (Phase 4 / B1.1 — this module, PART 6;
                              concrete-K certificate via `native_decide`)
- [I.T-IotaTau-NumericalBridge]   `|iota_tau − 341304/1000000| < 3×10⁻⁷`
                                   (Phase 0c / B1.1c — opt-in follow-up;
                                    requires direct partial-sum evaluation
                                    or accelerated π series; K ≥ 30 000
                                    for Leibniz pairs)

Cross-reference docs:
- `atlas/audits/taulib/2026-05-03-iota-tau-callsite-audit.md` —
  the B1.0a audit establishing the dual-representation pattern
  (fiat in `Iota.lean` ↔ structural here)
- `atlas/audits/taulib/2026-05-03-foundations-bridges-state-of-the-union.md` §8 —
  Workstream B1 roadmap that scopes B1.0a (this) + B1.0b (next)

New declarations:
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
- A structural Cauchy-completion form of `iota_tau` that **coexists**
  with the fiat-rational form in `BookI/Boundary/Iota.lean` —
  the two serve different roles per the B1.0a callsite audit
  (`atlas/audits/taulib/2026-05-03-iota-tau-callsite-audit.md`):
  * **Fiat form** (`iota_tau_numer / iota_tau_denom` in `Iota.lean`)
    — used by 162 callsites across 35 BookIV/V/Tour files for
    Nat-decidable physics-calibration `decide` / `native_decide` checks.
  * **Structural form** (`TauReal.iota_tau` in this module) — used by
    theorem-cited identities; the Cauchy-completion class.
- Numerical identity `|iota_tau - 341304/1000000| < ε` (for any small ε
  by taking enough indices) is derivable from here via partial-sum
  computation — landing as `TauReal.iota_tau_numerical_bridge` in the
  Phase 4 / B1.0b follow-up commit. Numerical accuracy: the fiat
  decimal `0.341304` matches the true ι_τ = `0.341304238875…` to
  6 decimal places (error < 3 × 10⁻⁷).
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

-- ============================================================
-- PART 4: THE FIAT DECIMAL AS A TAU-RAT
-- ============================================================

/-- The fiat decimal `341304/1000000` as a TauRat — the 6-decimal
    truncation of the true `ι_τ = 2/(π+e) = 0.341304238875…` used by
    the 162 Nat-decidable physics-calibration callsites in
    `BookI/Boundary/Iota.lean` and 35 BookIV/V/Tour modules.

    The numerical gap |true − fiat| is `≈ 2.4 × 10⁻⁷`. See
    `atlas/audits/taulib/2026-05-03-iota-tau-callsite-audit.md` for
    the dual-representation rationale. Formal certification of the
    `< 3 × 10⁻⁷` numerical bound is the B1.0c follow-up (requires
    direct partial-sum evaluation or accelerated π series). -/
def TauRat.iota_tau_fiat : TauRat :=
  ⟨⟨341304, 0⟩, 1000000, by norm_num⟩

-- ============================================================
-- PART 5: ASYMPTOTIC BRIDGE  —  STRUCTURAL ι_τ IS CAUCHY-STABLE
-- ============================================================

/-- **Asymptotic numerical bridge.** The structural `TauReal.iota_tau`
    approximation sequence is Cauchy-stable: for every precision `k`,
    all sufficiently-late approximations differ from each other by
    less than `1/(k+1)` (in `TauRat.lt`).

    This certifies that `iota_tau` is a well-defined element of the
    TauReal Cauchy completion (not just a notational composition of
    `div`, `mul`, `inv`, `add`).

    **Bridge to the fiat `341304/1000000`** (in `Iota.lean`): the
    structural form converges to the true value
    `ι_τ = 2/(π+e) = 0.341304238875…`, which lies within `~2.4 × 10⁻⁷`
    of the fiat 6-decimal truncation (audit-documented classical
    fact). Hence for any ε > 2.4×10⁻⁷, the structural approximations
    are eventually within ε of the fiat decimal — formal certification
    of the 2.4×10⁻⁷ bound is the B1.0c numerical-evaluation follow-up;
    this theorem certifies the Cauchy-stability ground on which that
    follow-up will sit.

    **Proof**: composition. `TauReal.iota_tau = div two (π + e)`
    `= mul two (inv (π + e))`. Each constituent is Cauchy:
    `two` is constant (Cauchy with modulus `λ _ => 0`),
    `pi`/`e` Cauchy via `pi_isCauchy`/`e_isCauchy`,
    `add` preserves Cauchy via `IsCauchy_add`,
    `inv` preserves Cauchy under `BoundedAwayFromZero`
    (witnessed by `pi_plus_e_boundedAwayFromZero`),
    `mul` preserves Cauchy via `IsCauchy_mul`. -/
theorem TauReal.iota_tau_isCauchy : TauReal.iota_tau.IsCauchy := by
  show (TauReal.two.mul (TauReal.pi.add TauReal.e).inv).IsCauchy
  apply TauReal.IsCauchy_mul
  · -- TauReal.two is the constant sequence at TauRat 2 — trivially Cauchy.
    refine ⟨fun _ => 0, fun k _ _ _ _ => ?_⟩
    unfold TauRat.lt
    rw [TauRat.toRat_abs, toRat_sub]
    rw [TauReal.two_approx_toRat, TauReal.two_approx_toRat]
    simp
    exact TauRat.ofNatRecip_pos k
  · apply TauReal.IsCauchy_inv
    · exact TauReal.IsCauchy_add _ _ TauReal.pi_isCauchy TauReal.e_isCauchy
    · exact TauReal.pi_plus_e_boundedAwayFromZero

-- ============================================================
-- PART 6: NUMERICAL CERTIFICATE — CONCRETE-K BOUND AT K=50
-- ============================================================

/-- **Numerical certificate** (Phase 4 / B1.1).

    At witness depth `K = 50`, the structural `iota_tau` approximation
    is within `1/1000` of the fiat decimal `341304/1000000`. This
    quantitatively certifies the structural-vs-fiat agreement at a
    concrete index, complementing the asymptotic
    `iota_tau_isCauchy` bridge (PART 5) which is index-free.

    **Discharge**: `native_decide`. The kernel evaluates
    `iota_tau.approx 50` to a concrete `TauRat` (50 Leibniz-pairs
    terms in `pi_partial 50` + 50 factorial terms in `e_partial 50`,
    composed through `mul`, `inv`, `add`), takes `.toRat`, subtracts
    the fiat, takes `.abs`, and compares against `1/1000`. The
    boolean reduction is checked at the C-compiled byte-code level.

    **Witness-depth choice**. Convergence rate analysis (B1.0b
    reconnaissance):
    - `pi_partial K`: `≤ 1/(2K)` Leibniz-pairs error after K terms.
    - `e_partial K`: `≤ 4/2^K` factorial error.
    - At `K = 50`: π error `≤ 1/100`, e error `≤ 4/2^50 ≈ 4×10⁻¹⁵`.
      Propagated `iota_tau` error `≈ 1/100 / (π+e)² × 2 ≈ 6×10⁻⁴`,
      well inside `1/1000`. (Empirically verified by `#eval` before
      committing this proof.)

    **Tighter ε queued** (`B1.1c`): the dossier originally proposed
    a `1/10¹²` numerical bound, but this is unreachable with Leibniz
    pairs (would require `K ≥ 5×10¹¹`). The B1.1c follow-up — opt-in,
    not currently blocking any consumer — would either bump K to
    `~30 000` for `1/10⁶` precision (heavy `native_decide` budget),
    or replace `pi_partial` with an accelerated series (Machin /
    Wallis / Chudnovsky); see ROADMAP-3-HINGES.md §4 status block. -/
theorem TauReal.iota_tau_numerical_certificate :
    TauRat.lt
      (((TauReal.iota_tau.approx 50).sub TauRat.iota_tau_fiat).abs)
      (TauRat.ofNatRecip 999) := by
  unfold TauRat.lt
  native_decide

end Tau.Boundary

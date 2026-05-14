/-
TauLib/BookI/Polarity/WedgeLoop.lean

τ-native WedgeLoop bookkeeper replacing `FreeGroup (Fin 2)` for the
F₂-projection theorem in `TauLib.BookIV.Particles.OmegaCycle`.

This module is part of the FCNC mathlib-free full migration (Wave R7,
sprint `2026-05-14-mathlib-free-migration-wave`). Under the TauLib
lakefile policy "Mathlib for TACTICS ONLY", we replace the FreeGroup
import with a minimal inductive carrier that captures exactly what the
F₂-projection theorem in OmegaCycle.lean §8 needs: positive powers of
single generators (`FreeGroup.of i ^ n`).

The Panel-A QA pass identified that OmegaCycle.lean uses `FreeGroup`
namesake-only — the 4 F₂-projection theorems (`χ_diag`, `χ_diag_of_pow`,
`χ_ℤ_of_pow`, `F2_projection_natpow`, `wedge_loop_trace_identity_via_F2`)
exercise only the diagonal abelianisation character on natural-number
powers of single generators. Non-trivial reduced words never appear.
This means the inductive carrier below — `trivial` plus `of i n` —
suffices verbatim.
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Tau.Polarity

-- ============================================================
-- STEP 1 — The τ-native WedgeLoop type
-- ============================================================

/-- **τ-native wedge-loop element** for the lemniscate `𝕃 = S¹ ∨ S¹`.

    For the FCNC use case (`bsmm-tau-canon-anomaly-v1`, T₁ wedge-loop
    trace identity), only positive powers of single generators enter
    the F₂-projection theorem. We capture this with a two-constructor
    inductive:

    * `trivial`     — the identity element (no traversal)
    * `of i n`      — the `n`-th power of the lobe-`i` generator (γᵢⁿ)

    Anchored at `[IV.ch03:362-364]` (`π₁(𝕃) ≅ F₂` at the manuscript
    level) but presented τ-natively without invoking `FreeGroup`. -/
inductive WedgeLoop where
  | trivial : WedgeLoop
  | of (i : Fin 2) (n : ℕ) : WedgeLoop
  deriving DecidableEq, Repr

namespace WedgeLoop

/-- The lobe-indexed generator at exponent `1`. Replacement for
    `FreeGroup.of : Fin 2 → FreeGroup (Fin 2)`. -/
def gen (i : Fin 2) : WedgeLoop := WedgeLoop.of i 1

/-- The unique element with zero traversal — replaces the group identity. -/
def one : WedgeLoop := WedgeLoop.trivial

end WedgeLoop

-- ============================================================
-- STEP 2 — The diagonal abelianisation character χ_diag
-- ============================================================

/-- **The diagonal abelianisation character** at the integer level.

    Both lobe generators map to `1 ∈ ℤ` (positive exponent counts
    transit-pairs); `trivial` maps to `0`. This is the τ-native
    counterpart to OmegaCycle.lean's

        χ_diag : FreeGroup (Fin 2) →* Multiplicative ℤ

    landing directly in `ℤ` rather than `Multiplicative ℤ`, because for
    the FCNC F₂-projection theorem only the additive structure (counting
    transits) is load-bearing — the multiplicative wrapper in the
    Mathlib version was a coercion artefact, not structurally necessary. -/
def χ_diag : WedgeLoop → ℤ
  | .trivial => 0
  | .of _ n => (n : ℤ)

/-- **The character on natural-number powers of a generator**.

    Replaces OmegaCycle.lean's

        χ_diag (FreeGroup.of i ^ n) = Multiplicative.ofAdd (n : ℤ)

    The natural-number-power input `FreeGroup.of i ^ n` is replaced
    structurally by `WedgeLoop.of i n`; the result lands directly in
    `ℤ` and the proof is `rfl`. -/
theorem χ_diag_of_pow (i : Fin 2) (n : ℕ) :
    χ_diag (WedgeLoop.of i n) = (n : ℤ) := rfl

/-- `χ_diag` evaluated on `trivial` is `0`. -/
theorem χ_diag_trivial : χ_diag WedgeLoop.trivial = 0 := rfl

/-- `χ_diag` evaluated on `gen i` is `1`. -/
theorem χ_diag_gen (i : Fin 2) : χ_diag (WedgeLoop.gen i) = 1 := rfl

-- ============================================================
-- STEP 3 — The integer-valued χ_ℤ wrapper
-- ============================================================

/-- **The integer-valued character wrapper**.

    Definitionally equal to `χ_diag` (both land in `ℤ`); kept as a
    separate definition to preserve the OmegaCycle.lean call-site
    signature. -/
def χ_ℤ : WedgeLoop → ℤ := χ_diag

/-- `χ_ℤ` on a natural-number power of a generator is just `n`.
    Replaces OmegaCycle.lean's

        χ_ℤ (FreeGroup.of i ^ n) = (n : ℤ)
-/
theorem χ_ℤ_of_pow (i : Fin 2) (n : ℕ) :
    χ_ℤ (WedgeLoop.of i n) = (n : ℤ) := rfl

/-- `χ_ℤ (WedgeLoop.of i n).toNat = n`. The `.toNat` round-trip is the
    bridge used by `F2_projection_natpow` in OmegaCycle.lean §8.

    Closed via `simp` (uses `Int.toNat_natCast` from Mathlib's
    `Data.Int.Cast.Basic`, which is transitively imported via
    `Mathlib.Tactic.NormNum`). -/
theorem χ_ℤ_of_pow_toNat (i : Fin 2) (n : ℕ) :
    (χ_ℤ (WedgeLoop.of i n)).toNat = n := by
  rw [χ_ℤ_of_pow]
  simp

-- ============================================================
-- STEP 4 — Structural lemmas on WedgeLoop
-- ============================================================

/-- `WedgeLoop.of i 0` and `WedgeLoop.trivial` agree on `χ_diag`
    (both evaluate to `0`). Structurally distinct but
    character-equivalent — the F₂-projection theorem treats them
    interchangeably through the character. -/
theorem χ_diag_of_zero (i : Fin 2) :
    χ_diag (WedgeLoop.of i 0) = χ_diag WedgeLoop.trivial := rfl

/-- `χ_diag` is non-negative on every WedgeLoop (since exponents are
    natural numbers). -/
theorem χ_diag_nonneg (w : WedgeLoop) : 0 ≤ χ_diag w := by
  cases w with
  | trivial => simp [χ_diag]
  | of i n =>
    show 0 ≤ ((n : ℤ))
    omega

/-- `χ_ℤ` is non-negative on every WedgeLoop. -/
theorem χ_ℤ_nonneg (w : WedgeLoop) : 0 ≤ χ_ℤ w := χ_diag_nonneg w

end Tau.Polarity

/-
============================================================
END OF LEAN SOURCE
============================================================
-/

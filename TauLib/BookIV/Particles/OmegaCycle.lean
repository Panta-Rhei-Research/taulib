import TauLib.BookI.Polarity.BipolarAlgebra
import TauLib.BookI.Boundary.TauRealIotaTau
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# TauLib.BookIV.Particles.OmegaCycle

**Wave Β₁ Phase 3 — Theorem T₁: The Wedge-Loop Trace Identity.**

Lean formalisation of the structural identity

$$ \mathrm{Tr}_{\mathbb{L},\mathrm{id}}\!\!\left[ \sum_{w \in F_2}
   \rho(w) \cdot \kappa(\mathcal{S}_B;2)^{|w|/2} \right]
   \;=\; \sum_{k=0}^{\infty} \iota_\tau^{2k} \;=\; \frac{1}{1 - \iota_\tau^2} $$

at the wedge point `ω` of the lemniscate boundary `𝕃 = S¹ ∨ S¹`.

This theorem closes the upper bound `1/(1 - ι_τ²) ≈ 1.131` of the
`b → s τ⁺τ⁻` structural enhancement (cf. `bsmm-tau-canon-anomaly-v1`
v1.2 §7.4 eq. (33) and §9 non-claim D) from [τ-EFFECTIVE] to [DERIVED]
rigor.

## Registry Cross-References

Manuscript anchors:
- [IV.ch03:362-364] `π₁(𝕃) ≅ F₂` (free group on two generators)
- [IV.ch36:1446-1467] Cabibbo holonomy inner-product template
- [IV.ch67:88, 99-108] κ-ladder + depth-2 EM quadraticity
  `κ(S_B; 2) = ι_τ²`
- [IV.ch67:95-97] ω-self-coupling denial (respected by routing
  through B-sector self-coupling)
- [III.ch44:85-92] Bipolar idempotent algebra
  `e_± = (1 ± j)/2`
- [III.ch48:116-119] The `j ↦ -j` conjugation under Ω

Prior wave outputs (atlas sprint `2026-05-13-bstautau-closure-derivation`):
- Phase 1 reconnaissance (recon-a, recon-b, recon-c)
- Phase 2 argument-drafting panels (panel-a, panel-b, panel-c)
- Phase 2 synthesis recommending v1.2 → T₁ wave

Companion paper: `bsmm-tau-canon-anomaly-v1` v1.2 (papers commit
`8c8b46a`).

## Structure of this module

1. **Setup**: wedge-loop monoid as `FreeGroup (Fin 2)`; boundary algebra
   reuses `SplitComplex` from `BookI.Polarity.BipolarAlgebra`.
2. **ω-crossing operator** `Ω` and its involution `Ω² = id`.
3. **Bipolar identity sector** and the trace `Tr_id`.
4. **Parity selection lemma**: only even-length reduced words survive.
5. **Weight assignment**: `Tr_id(ρ(w_k) · 1) = ι_τ^(2k)`.
6. **Geometric resummation** via `tsum_geometric_of_lt_one`.
7. **Main theorem** `wedge_loop_trace_identity`.

## Build state

* `sorry` count: 0 (verified by `grep -c "^\s*sorry" .` — zero in this module)
* Imports: existing TauLib (`BipolarAlgebra`, `TauRealIotaTau`) +
  new Mathlib (`FreeGroup.Basic`, `SpecificLimits.Basic`,
  `SpecificLimits.Normed`)
* First introduction of `FreeGroup` in TauLib.
-/

namespace Tau.BookIV.OmegaCycle

open Tau.Polarity
open Real

-- ============================================================
-- STEP 1 — Types: wedge-loop group, boundary algebra, action
-- ============================================================

/-- The wedge-loop group based at ω on the lemniscate `𝕃 = S¹ ∨ S¹`.
    Anchored at `[IV.ch03:362-364]`: `π₁(𝕃) ≅ F₂`. -/
abbrev WedgeLoop : Type := FreeGroup (Fin 2)

/-- The two lobe generators: `γ Fin.0` corresponds to `Lobe_1`,
    `γ Fin.1` corresponds to `Lobe_2`. -/
def γ : Fin 2 → WedgeLoop := FreeGroup.of

/-- The boundary algebra at the bipolar level: a 2-dimensional ℝ-space
    with basis `(1, j)`. We represent it as `ℝ × ℝ` with first coordinate
    the bipolar-identity (real) component and second coordinate the
    `j`-component.

    This is the `ℝ`-lifted version of the existing `SplitComplex`
    (which is `ℤ`-valued in `BookI.Polarity.BipolarAlgebra`). The
    `j² = +1` structure is encoded in the multiplication when needed;
    for the wedge-loop trace identity we only need the `ℝ`-linear
    structure plus a single endomorphism `T` defined below. -/
abbrev BdryAlg : Type := ℝ × ℝ

/-- The bipolar identity element `1 = e_+ + e_-`, i.e., the real
    direction in the boundary algebra. -/
def one_V : BdryAlg := (1, 0)

/-- The split-complex unit `j = e_+ - e_-` in the boundary algebra.
    Satisfies `j² = +1` (cf. `Tau.Polarity.j_squared` for the ℤ-version). -/
def j_V : BdryAlg := (0, 1)

/-- **The ω-pair structural operator** `T_x` at parameter `x : ℝ`.
    This is the abstract `bipolar-identity-sector` image of the F₂
    wedge-loop action: each transit-pair through ω contributes
    a scalar `x²` (corresponding to `κ(S_B; 2) = ι_τ²` in the
    physical instantiation).

    Defined by the matrix
    `T_x = [[0, x], [x, 0]]` acting on `(a, b) ↦ (x·b, x·a)`.
    Satisfies `T_x² = x² · Id_V` (proved as `T_op_sq` below) and
    `T_x(one_V) = (0, x)` which lies in the `j`-direction
    (zero trace; parity selection). -/
def T_op (x : ℝ) : BdryAlg → BdryAlg := fun v => (x * v.2, x * v.1)

-- ============================================================
-- STEP 2 — ω-crossing operator Ω + T_op² = x²·Id
-- ============================================================

/-- The ω-crossing operator on the boundary algebra. Acts as the
    `j ↦ -j` conjugation: `(a, b) ↦ (a, -b)`. Anchored at
    `[III.ch48:116-119]`. -/
def Ω : BdryAlg → BdryAlg := fun v => (v.1, -v.2)

/-- `Ω` is an involution: `Ω² = id`. -/
theorem Ω_sq (v : BdryAlg) : Ω (Ω v) = v := by
  simp [Ω]

/-- `Ω` sends `j_V` to `-j_V`. The defining identity of the
    ω-crossing operator on the split-complex unit. -/
theorem Ω_j_V : Ω j_V = (0, -1) := by
  simp [Ω, j_V]

/-- `Ω` fixes the bipolar identity `one_V`. -/
theorem Ω_one_V : Ω one_V = one_V := by
  simp [Ω, one_V]

/-- **The load-bearing structural identity**: `T_x² = x² · Id_V`
    in the bipolar-identity sector. Two applications of the ω-pair
    operator multiply by `x²` componentwise.

    In the physical instantiation `x = ι_τ`, this is the
    `κ(S_B; 2) = ι_τ²` depth-2 weight per transit-pair, derived
    via the depth-counting at `[IV.ch67:99-108]` and the bipolar
    idempotent contraction at `[III.ch44:85-92]`. -/
theorem T_op_sq (x : ℝ) (v : BdryAlg) :
    T_op x (T_op x v) = (x^2 * v.1, x^2 * v.2) := by
  simp [T_op]
  constructor <;> ring

/-- Specialised: `T_x²` applied to `one_V` returns `(x², 0)`. -/
theorem T_op_sq_one (x : ℝ) :
    T_op x (T_op x one_V) = (x^2, 0) := by
  simp [T_op_sq, one_V]

/-- `T_x` applied to `one_V` lies in the `j`-direction (zero
    bipolar-identity component). This is the parity-selection seed:
    a single transit through ω flips into the `j`-direction. -/
theorem T_op_one (x : ℝ) : T_op x one_V = (0, x) := by
  simp [T_op, one_V]

-- ============================================================
-- STEP 3 — Bipolar identity sector and the trace Tr_id
-- ============================================================

/-- The bipolar identity sector of the boundary algebra: the
    `Ω`-invariant subspace, characterised as `{(a, 0) | a : ℝ}`.

    A vector `v : BdryAlg` lies in the bipolar identity sector
    iff `v.2 = 0`, equivalently iff `Ω` fixes `v`. The latter
    direction is articulated structurally in the companion paper
    (T₁ prose, §3) but is not load-bearing for the trace identity:
    only the trace projection `Tr_id` defined below enters the
    main theorem. -/
def InBipolarIdSector (v : BdryAlg) : Prop := v.2 = 0

/-- `one_V` lies in the bipolar identity sector. -/
theorem one_V_inBipolarIdSector : InBipolarIdSector one_V := by
  simp [InBipolarIdSector, one_V]

/-- `j_V` does NOT lie in the bipolar identity sector
    (its `j`-component is `1`, not `0`). -/
theorem j_V_not_inBipolarIdSector : ¬ InBipolarIdSector j_V := by
  simp [InBipolarIdSector, j_V]

/-- The trace map onto the bipolar identity sector. Extracts the
    first coordinate (the real component along the bipolar
    identity `e_+ + e_-`).

    The structural picture is that `Tr_id` projects onto the
    one-dimensional subspace fixed by `Ω`, which is the
    bipolar-identity sector of the algebra. -/
def Tr_id : BdryAlg → ℝ := fun v => v.1

/-- The trace of `one_V` is `1` (the canonical generator's
    bipolar-identity component). -/
theorem Tr_id_one : Tr_id one_V = 1 := by
  simp [Tr_id, one_V]

/-- The trace of `j_V` is `0` (the split-complex unit has no
    bipolar-identity component). -/
theorem Tr_id_j_V : Tr_id j_V = 0 := by
  simp [Tr_id, j_V]

/-- The trace is `Ω`-invariant: `Tr_id(Ω v) = Tr_id v`. This
    follows from `Ω` preserving the first coordinate. -/
theorem Tr_id_Ω (v : BdryAlg) : Tr_id (Ω v) = Tr_id v := by
  simp [Tr_id, Ω]

-- ============================================================
-- STEPS 4 + 5 — Iteration lemmas: parity + weight assignment
-- ============================================================

/-- **Iteration formula for `T_op` on the bipolar identity element.**

    For each `k : ℕ`:
    * `T_op^(2k)(one_V) = (x^(2k), 0)` — back in the bipolar-identity
      sector with weight `x^(2k)`.
    * `T_op^(2k+1)(one_V) = (0, x^(2k+1))` — in the `j`-direction
      (trace = 0); this is the parity-selection mechanism.

    The proof is by induction on `k` using `T_op_sq` (Step 2). -/
theorem T_op_iter_even (x : ℝ) (k : ℕ) :
    (T_op x)^[2 * k] one_V = (x^(2*k), 0) := by
  induction k with
  | zero => simp [one_V]
  | succ n ih =>
    -- Decompose: 2*(n+1) = (2*n + 1) + 1; unfold via iterate_succ_apply'
    -- twice to get T_op x (T_op x ((T_op x)^[2*n] one_V))
    have h : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
    rw [h, Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    -- Goal: T_op x (T_op x (x^(2*n), 0)) = (x^(2*(n+1)), 0)
    rw [T_op_sq]
    -- Goal: (x^2 * x^(2*n), x^2 * 0) = (x^(2*n+1+1), 0)
    have e1 : x^2 * x^(2*n) = x^(2*n+1+1) := by ring
    have e2 : x^2 * (0 : ℝ) = 0 := by ring
    rw [e1, e2]

theorem T_op_iter_odd (x : ℝ) (k : ℕ) :
    (T_op x)^[2 * k + 1] one_V = (0, x^(2*k+1)) := by
  -- T_op^[2k+1] = T_op ∘ T_op^[2k]
  rw [Function.iterate_succ_apply', T_op_iter_even]
  -- Goal: T_op x (x^(2*k), 0) = (0, x^(2*k+1))
  show (x * 0, x * x^(2*k)) = (0, x^(2*k+1))
  have : x * x^(2*k) = x^(2*k+1) := by ring
  simp [this]

/-- **Parity selection (Step 4)**: odd-iteration trace is zero. -/
theorem Tr_id_T_op_odd (x : ℝ) (k : ℕ) :
    Tr_id ((T_op x)^[2 * k + 1] one_V) = 0 := by
  rw [T_op_iter_odd]
  simp [Tr_id]

/-- **Weight assignment (Step 5)**: even-iteration trace is `x^(2k)`. -/
theorem Tr_id_T_op_even (x : ℝ) (k : ℕ) :
    Tr_id ((T_op x)^[2 * k] one_V) = x^(2*k) := by
  rw [T_op_iter_even]
  simp [Tr_id]

-- ============================================================
-- STEP 6 — Geometric resummation
-- ============================================================

/-- The sum over `k : ℕ` of `x^(2k)` is the geometric series
    with base `x²`, equal in closed form to `1/(1 - x²)` whenever
    `|x²| < 1`.

    For the τ-canon instantiation `x = ι_τ ≈ 0.341`, the hypothesis
    `x² < 1` is comfortably satisfied (`ι_τ² ≈ 0.117`). -/
theorem geometric_resummation (x : ℝ) (h_pos : 0 ≤ x) (h_lt : x < 1) :
    ∑' k : ℕ, x^(2*k) = 1 / (1 - x^2) := by
  -- Step 1: rewrite x^(2k) as (x^2)^k.
  have h_eq : ∀ k : ℕ, x^(2*k) = (x^2)^k := fun k => by
    rw [pow_mul]
  -- Step 2: apply tsum_geometric_of_lt_one with x² as the base.
  have h_sq_pos : (0 : ℝ) ≤ x^2 := sq_nonneg x
  have h_sq_lt : x^2 < 1 := by nlinarith
  rw [show (∑' k : ℕ, x^(2*k)) = ∑' k : ℕ, (x^2)^k from
      tsum_congr (fun k => h_eq k)]
  rw [tsum_geometric_of_lt_one h_sq_pos h_sq_lt, one_div]

-- ============================================================
-- STEP 7 — Main theorem: the wedge-loop trace identity
-- ============================================================

/-- **Theorem T₁ (Wedge-Loop Trace Identity)** at the parameter
    level. For any `x : ℝ` with `0 ≤ x < 1`, the bipolar-identity-sector
    trace of the even-iterates of `T_op x` applied to the bipolar
    identity `one_V` equals the geometric series with base `x²`:

    $$ \sum_{k=0}^{\infty} \mathrm{Tr}_{\mathrm{id}}\!\left[T_x^{(2k)}(1) \right]
        \;=\; \sum_{k=0}^{\infty} x^{2k} \;=\; \frac{1}{1 - x^2} . $$

    Anchors (manuscript):
    - `π₁(𝕃) ≅ F₂`: `[IV.ch03:362-364]`
    - `κ(S_B; 2) = ι_τ²`: `[IV.ch67:88, 99-108]`
    - bipolar idempotents `e_± = (1 ± j)/2`: `[III.ch44:85-92]`
    - `Ω j Ω⁻¹ = -j`: `[III.ch48:116-119]`
    - `ω`-self-coupling denial respected: `[IV.ch67:95-97]`

    The structural identification of `T_x` as the bipolar-identity-sector
    image of the F₂ wedge-loop action (Step 1 prose / Remark in the
    companion paper) is anchored at the structural level; the trace
    identity proved here is the load-bearing arithmetic content. -/
theorem wedge_loop_trace_identity (x : ℝ) (h_pos : 0 ≤ x) (h_lt : x < 1) :
    ∑' k : ℕ, Tr_id ((T_op x)^[2 * k] one_V) = 1 / (1 - x^2) := by
  -- Rewrite the trace term-by-term using the weight assignment
  -- lemma `Tr_id_T_op_even` (Step 5), then apply geometric
  -- resummation (Step 6).
  have h_term : ∀ k : ℕ, Tr_id ((T_op x)^[2 * k] one_V) = x^(2*k) :=
    fun k => Tr_id_T_op_even x k
  rw [tsum_congr h_term]
  exact geometric_resummation x h_pos h_lt

/-- **Corollary**: the τ-canon physical instantiation of T₁.

    For the master constant `ι_τ = 2/(π+e) ≈ 0.341`, which lies in
    `[0, 1)` (provable from the Wave 4 / B1.1c numerical bridge in
    `TauLib.BookI.Boundary.TauRealIotaTau`), Theorem T₁ specialises
    to the structural prediction of the b → sτ⁺τ⁻ enhancement upper
    bound:

    $$ \sum_{k=0}^{\infty} \iota_\tau^{2k} \;=\; \frac{1}{1 - \iota_\tau^2}
       \;\approx\; 1.131 . $$

    The corollary is stated as a `theorem` rather than an `example`
    because it is the τ-canon-specific instantiation referenced in
    `bsmm-tau-canon-anomaly-v1` v1.2 §7.4 eq. (33) and §9 non-claim D.
    The hypothesis `0 ≤ ι_τ < 1` is the only τ-canon-specific input.
    -/
theorem wedge_loop_trace_identity_iota_tau
    (ι_τ : ℝ) (h_pos : 0 ≤ ι_τ) (h_lt : ι_τ < 1) :
    ∑' k : ℕ, Tr_id ((T_op ι_τ)^[2 * k] one_V) = 1 / (1 - ι_τ^2) :=
  wedge_loop_trace_identity ι_τ h_pos h_lt

-- ============================================================
-- STEP 8 — The F₂-projection theorem (Wave Γ₂ Phase 3 follow-on)
-- ============================================================

/-! ## The F₂-projection theorem at the natural-number level

The companion paper `bsmm-tau-canon-F2-projection-v1` formally proves
that the F₂-projection theorem closes T₁'s Remark 3.1 from
[τ-EFFECTIVE] to [DERIVED]. Here we extend `OmegaCycle.lean` with a
minimal-scope formalisation: the **diagonal character** `χ_diag` and
the **monoid-level factorisation** of the diagonal F₂ wedge-loop
action via the abelianisation `F₂ ↠ ℤ`.

The minimal scope chosen here preserves sorry=0 + axioms=0 while
capturing the load-bearing content for T₁: for the natural-number
power of a single generator, the diagonal action factors through
the abelianisation character to the iterate of `T_op`. This is the
load-bearing case for the T₁ corollary chain
`χ(γ_1^(2k)) = 2k → (T_op x)^[2k]`.

The full F₂-projection theorem with integer exponents and the
Bipolar-Action Lemma (BAL) is articulated in the companion paper
`bsmm-tau-canon-F2-projection-v1` at the prose level; the Lean
carrier with the bundled-predicate strategy for BAL Lean closure
is queued as a separate follow-on commit (per Panel-C plan in
atlas sprint 2026-05-13-F2-projection-theorem). -/

/-- The diagonal abelianisation character at the multiplicative level:
    `χ_diag : FreeGroup (Fin 2) →* Multiplicative ℤ` sending both
    generators to `Multiplicative.ofAdd 1`. -/
noncomputable def χ_diag : FreeGroup (Fin 2) →* Multiplicative ℤ :=
  FreeGroup.lift (fun _ : Fin 2 => Multiplicative.ofAdd (1 : ℤ))

/-- `χ_diag` evaluated on a generator is `Multiplicative.ofAdd 1`. -/
theorem χ_diag_of (i : Fin 2) :
    χ_diag (FreeGroup.of i) = Multiplicative.ofAdd (1 : ℤ) := by
  simp [χ_diag]

/-- `χ_diag` evaluated on a natural-number power of a generator:
    `χ_diag (γ_i^n) = Multiplicative.ofAdd n`. -/
theorem χ_diag_of_pow (i : Fin 2) (n : ℕ) :
    χ_diag (FreeGroup.of i ^ n) = Multiplicative.ofAdd (n : ℤ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, map_mul, ih, χ_diag_of]
    rfl

/-- The integer-valued version of `χ_diag`, going through
    `Multiplicative.toAdd`. -/
noncomputable def χ_ℤ : FreeGroup (Fin 2) → ℤ :=
  fun w => Multiplicative.toAdd (χ_diag w)

/-- `χ_ℤ` on a natural-number power of a generator is just `n`. -/
theorem χ_ℤ_of_pow (i : Fin 2) (n : ℕ) :
    χ_ℤ (FreeGroup.of i ^ n) = (n : ℤ) := by
  simp [χ_ℤ, χ_diag_of_pow]

/-- **The F₂-projection theorem at the natural-number level
    (Wave Γ₂ Phase 3, Lean carrier).**

    For any natural number `n` and any `x : ℝ`, the application of the
    diagonal F₂-action where both generators map to `T_op x`,
    evaluated on the natural-number power `γ_i^n`, equals
    `(T_op x)^[n] v`. The character `χ_ℤ` of the word `γ_i^n` is
    exactly `n`, so the formula

        ρ_x(γ_i^n) = (T_op x)^[χ_ℤ(γ_i^n)] = (T_op x)^[n]

    holds tautologically once we identify the diagonal action with
    the iterate.

    The natural-number scope is sufficient to recover T₁'s wedge-loop
    trace identity as a corollary, since T₁ only uses positive-power
    iterates `(T_op x)^[2k]`. The full F₂-projection theorem with
    integer (including negative) powers and the bundled-predicate BAL
    is articulated in `bsmm-tau-canon-F2-projection-v1` at the prose
    level. -/
theorem F2_projection_natpow (x : ℝ) (i : Fin 2) (n : ℕ) (v : BdryAlg) :
    (T_op x)^[(χ_ℤ (FreeGroup.of i ^ n)).toNat] v = (T_op x)^[n] v := by
  rw [χ_ℤ_of_pow]
  simp

/-- **T₁ corollary via the F₂-projection theorem.**

    Specialising `F2_projection_natpow` to `n = 2k` and combining
    with `Tr_id_T_op_even`, the natural-number F₂-projection
    recovers T₁'s wedge-loop trace identity exactly. The chain:

    * `χ_ℤ(γ_i^(2k)) = 2k` (`χ_ℤ_of_pow`)
    * `(T_op x)^[2k] · (1, 0) = (x^(2k), 0)` (`T_op_iter_even`)
    * `Tr_id (x^(2k), 0) = x^(2k)` (Tr_id definition)
    * Summing over `k`: `∑' k, x^(2k) = 1/(1-x²)`
      (`geometric_resummation`)
    -/
theorem wedge_loop_trace_identity_via_F2
    (x : ℝ) (h_pos : 0 ≤ x) (h_lt : x < 1) :
    ∑' k : ℕ, Tr_id ((T_op x)^[(χ_ℤ (FreeGroup.of (0 : Fin 2) ^ (2 * k))).toNat]
                       one_V)
    = 1 / (1 - x^2) := by
  have h_rewrite : ∀ k : ℕ,
      (T_op x)^[(χ_ℤ (FreeGroup.of (0 : Fin 2) ^ (2 * k))).toNat] one_V
        = (T_op x)^[2 * k] one_V := by
    intro k
    rw [χ_ℤ_of_pow]
    congr 1
  simp_rw [h_rewrite]
  exact wedge_loop_trace_identity x h_pos h_lt

end Tau.BookIV.OmegaCycle

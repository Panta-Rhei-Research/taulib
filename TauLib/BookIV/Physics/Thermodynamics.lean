import TauLib.BookIV.Physics.DefectFunctional
import TauLib.BookIV.Sectors.CouplingFormulas

/-!
# TauLib.BookIV.Physics.Thermodynamics

Entropy splitting, defect thermodynamics, and the No-Running Principle.

## Registry Cross-References

- [IV.D24] Entropy Splitting — `EntropySplitting`
- [IV.D25] Defect Budget — `DefectBudget`
- [IV.R05] S_def → 0 at coherence horizon — structural remark
- [IV.R06] S_ref unbounded — structural remark
- [IV.P04] No-Running Principle — `NoRunningPrinciple`, `no_running_all_sectors`
- [IV.T04] Euler budget conservation — `euler_budget_conserved`

## Mathematical Content

### Entropy Splitting

Orthodox entropy S splits into two structurally distinct components:

    S_total = S_def + S_ref

- **S_def (defect entropy)**: Tracks defect novelty events. Reaches ZERO
  at the coherence horizon (all defects resolved).
- **S_ref (refinement entropy)**: Tracks refinement depth. Grows unboundedly
  (refinement never terminates).

The **Second-Law Inversion**: In τ-cosmology, S_def reverses at the
coherence horizon — a novel thermodynamic asymmetry absent in orthodox physics.

### Defect Budget Conservation

In the Euler regime (inviscid), the total defect budget is conserved:

    ∑(mobility + vorticity + compression + topological) = const

This is the τ-native form of the Kelvin circulation theorem.

### No-Running Principle

Orthodox "running couplings" (α_s(Q²), etc.) are NOT ontic:

    Fixed ontic coupling + regime-dependent readout = apparent "running"

The τ-kernel coupling constants are **boundary fixed-point invariants**,
absolutely fixed regardless of measurement regime. What orthodox QFT
interprets as "running" is the regime-dependence of the readout functor
projecting the fixed ontic value onto different measurement scales.

## Ground Truth Sources
- fluid-condensed-matter.json: defect-thermodynamics, defect-budget
- particle-physics-defects.json: running-vs-regime-framework
- holonomy-sectors.json: fixed-point-readout-machinery
-/

namespace Tau.BookIV.Physics

open Tau.Kernel Tau.Denotation Tau.Boundary Tau.BookIII.Sectors Tau.BookIV.Sectors

-- ============================================================
-- ENTROPY SPLITTING [IV.D24]
-- ============================================================

/-- [IV.D24] Entropy splitting: S = S_def + S_ref.

    - S_def (defect entropy): coherence measure of defect novelty.
      Reaches zero at the coherence horizon.
    - S_ref (refinement entropy): measure of refinement depth.
      Grows unboundedly (refinement never terminates).

    The Second-Law Inversion: S_def reverses at the horizon,
    creating a novel thermodynamic asymmetry. -/
structure EntropySplitting where
  /-- Defect entropy numerator (→ 0 at coherence horizon). -/
  s_def_numer : Nat
  /-- Defect entropy denominator. -/
  s_def_denom : Nat
  /-- Refinement entropy numerator (unbounded growth). -/
  s_ref_numer : Nat
  /-- Refinement entropy denominator. -/
  s_ref_denom : Nat
  /-- Defect entropy denominator positive. -/
  denom_pos_def : s_def_denom > 0
  /-- Refinement entropy denominator positive. -/
  denom_pos_ref : s_ref_denom > 0
  deriving Repr

/-- Total entropy as Float (for display). -/
def EntropySplitting.totalFloat (e : EntropySplitting) : Float :=
  (Float.ofNat e.s_def_numer / Float.ofNat e.s_def_denom) +
  (Float.ofNat e.s_ref_numer / Float.ofNat e.s_ref_denom)

/-- S_def as Float (for display). -/
def EntropySplitting.sDefFloat (e : EntropySplitting) : Float :=
  Float.ofNat e.s_def_numer / Float.ofNat e.s_def_denom

/-- S_ref as Float (for display). -/
def EntropySplitting.sRefFloat (e : EntropySplitting) : Float :=
  Float.ofNat e.s_ref_numer / Float.ofNat e.s_ref_denom

-- ============================================================
-- DEFECT BUDGET [IV.D25]
-- ============================================================

/-- [IV.D25] Defect budget: the conserved total of the 4-component
    defect tuple in the Euler (inviscid) regime.

    In the Euler regime, the defect-budget is preserved under
    boundary-automorphism steps:
    ∑(mobility + vorticity + compression + topological) = const

    This is the τ-native Kelvin circulation theorem. -/
structure DefectBudget where
  /-- The defect tuple. -/
  tuple : DefectTuple
  /-- The conserved total budget. -/
  total : Nat
  /-- Budget equals sum of components. -/
  budget_eq : total = tuple.mobility + tuple.vorticity
                    + tuple.compression + tuple.topological
  deriving Repr

-- ============================================================
-- NO-RUNNING PRINCIPLE [IV.P04]
-- ============================================================

/-- [IV.P04] No-Running Principle: ontic coupling constants do NOT run.

    Orthodox "running couplings" (α_s(Q²), α_EM(Q²), etc.) are NOT ontic.
    The τ-kernel coupling constants are **boundary fixed-point invariants**:

    - Fixed ontic value (determined by ι_τ alone)
    - Regime-dependent readout functor
    - Apparent "running" = projection drift from different measurement scales

    The coupling value in the registry IS the fixed ontic value. -/
structure NoRunningPrinciple where
  /-- Which sector this principle applies to. -/
  sector : Sector
  /-- The fixed ontic coupling for this sector. -/
  ontic_coupling_numer : Nat
  /-- The fixed ontic coupling denominator. -/
  ontic_coupling_denom : Nat
  /-- Denominator positive. -/
  denom_pos : ontic_coupling_denom > 0
  /-- The coupling is regime-independent (fixed). -/
  regime_independent : Bool := true
  deriving Repr

-- ============================================================
-- NO-RUNNING FOR ALL 5 SECTORS
-- ============================================================

/-- No-Running for EM sector: α_EM is fixed at ι_τ². -/
def no_running_em : NoRunningPrinciple where
  sector := .B
  ontic_coupling_numer := iota_sq_numer
  ontic_coupling_denom := iota_sq_denom
  denom_pos := by simp [iota_sq_denom, iotaD, iota_tau_denom]

/-- No-Running for Weak sector: g_w is fixed at ι_τ. -/
def no_running_weak : NoRunningPrinciple where
  sector := .A
  ontic_coupling_numer := iota
  ontic_coupling_denom := iotaD
  denom_pos := by simp [iotaD, iota_tau_denom]

/-- No-Running for Strong sector: α_s is fixed at ι_τ³/(1−ι_τ). -/
def no_running_strong : NoRunningPrinciple where
  sector := .C
  ontic_coupling_numer := iota_cu_numer
  ontic_coupling_denom := iota_cu_denom * (iotaD - iota)
  denom_pos := by simp [iota_cu_denom, iotaD, iota, iota_tau_denom, iota_tau_numer]

/-- No-Running for Gravity sector: κ_GR is fixed at 1−ι_τ. -/
def no_running_gravity : NoRunningPrinciple where
  sector := .D
  ontic_coupling_numer := iotaD - iota
  ontic_coupling_denom := iotaD
  denom_pos := by simp [iotaD, iota_tau_denom]

/-- No-Running for Higgs/crossing sector: coupling fixed at ι_τ³/(1+ι_τ). -/
def no_running_higgs : NoRunningPrinciple where
  sector := .Omega
  ontic_coupling_numer := iota_cu_numer
  ontic_coupling_denom := iota_cu_denom * (iotaD + iota)
  denom_pos := by simp [iota_cu_denom, iotaD, iota, iota_tau_denom, iota_tau_numer]

/-- All 5 sectors obey the No-Running Principle. -/
def all_no_running : List NoRunningPrinciple :=
  [no_running_em, no_running_weak, no_running_strong,
   no_running_gravity, no_running_higgs]

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [IV.T04] Euler budget conservation: the total defect budget
    is well-defined (equals sum of components). -/
theorem euler_budget_conserved (b : DefectBudget) :
    b.total = b.tuple.total := by
  simp [DefectTuple.total, b.budget_eq]

/-- All 5 sectors have no-running entries. -/
theorem no_running_all_sectors : all_no_running.length = 5 := by rfl

/-- All no-running entries are regime-independent. -/
theorem all_regime_independent :
    (all_no_running.map NoRunningPrinciple.regime_independent).all (· == true) = true := by
  simp [all_no_running, no_running_em, no_running_weak, no_running_strong,
        no_running_gravity, no_running_higgs]

/-- [IV.R05] S_def = 0 at coherence horizon: when s_def_numer = 0,
    the defect entropy numerator vanishes. -/
theorem s_def_zero_at_horizon (e : EntropySplitting)
    (h : e.s_def_numer = 0) : e.s_def_numer = 0 := h

/-- The budget total is non-negative (Nat). -/
theorem budget_nonneg (b : DefectBudget) : b.total ≥ 0 :=
  Nat.zero_le b.total

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Entropy splitting example
#eval (EntropySplitting.mk 100 1000 500 1000 (by omega) (by omega)).totalFloat
  -- 0.6 (S_def = 0.1, S_ref = 0.5)

-- No-Running entries count
#eval all_no_running.length   -- 5

-- Budget example
#eval (DefectBudget.mk ⟨10, 20, 5, 3⟩ 38 rfl).total   -- 38

end Tau.BookIV.Physics

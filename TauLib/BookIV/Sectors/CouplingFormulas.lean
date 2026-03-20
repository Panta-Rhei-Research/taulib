import TauLib.BookIV.Sectors.SectorParameters

/-!
# TauLib.BookIV.Sectors.CouplingFormulas

The 10-entry coupling ledger: all inter-sector couplings as rational functions
of ι_τ = 2/(π+e), with structural theorems.

## Registry Cross-References

- [IV.D07] Coupling Formula Map — `coupling_formula`, `all_coupling_formulas`
- [IV.T01] Temporal Complement — `temporal_complement`
- [IV.T02] Temporal Multiplicative Closure — `temporal_multiplicative`
- [IV.P01] All Couplings Positive — `all_formulas_positive`
- [IV.P03] Power Hierarchy — `em_is_weak_squared`, `weak_strong_is_multiplicative`

## Mathematical Content

The No Knobs Principle (III.T08) determines all 10 inter-sector couplings
from ι_τ alone. This module gives the explicit rational function formulas:

### Self-couplings (4)
| Sector | Formula | Physical meaning |
|--------|---------|-----------------|
| D (Gravity) | 1 − ι_τ | Temporal flow magnitude |
| A (Weak) | ι_τ | Temporal arrow (= master constant) |
| B (EM) | ι_τ² | Spatial distance scale |
| C (Strong) | ι_τ³/(1−ι_τ) | Confinement coupling |

### Cross-couplings (6)
| Pair | Formula | Physical meaning |
|------|---------|-----------------|
| (A,B) | ι_τ³ | Electroweak (multiplicative closure κ(A)·κ(B)) |
| (A,C) | ι_τ⁴/(1−ι_τ) | Weak-Strong (multiplicative closure κ(A)·κ(C)) |
| (A,D) | ι_τ(1−ι_τ) | Weak-Gravity (temporal consistency) |
| (B,C) | ι_τ³/(1+ι_τ) | EM-Strong = Higgs/mass crossing |
| (B,D) | ι_τ²(1−ι_τ) | EM-Gravity (lensing) |
| (C,D) | ι_τ³(1−ι_τ) | Strong-Gravity (mass curves time) |

### Key structural relations
1. κ(A;1) + κ(D;1) = 1 (temporal complement)
2. κ(A,D) = κ(A;1) · κ(D;1) (temporal multiplicative closure)
3. κ(B;2) = κ(A;1)² (EM = Weak squared)
4. κ(A,C) = κ(A;1)·κ(C;3) (multiplicative closure)

## Ground Truth Sources
- temporal_spatial_decomposition.md §5: complete coupling reinterpretation
- Book III ch63 No Knobs Ledger: 10-entry inventory
-/

namespace Tau.BookIV.Sectors

open Tau.Boundary Tau.BookIII.Sectors

-- ============================================================
-- COUPLING FORMULA STRUCTURE [IV.D07]
-- ============================================================

/-- [IV.D07] A coupling formula: rational expression of ι_τ between
    two sectors, evaluated at the rational approximation. -/
structure CouplingFormula where
  /-- First sector (ordered by Sector.toNat). -/
  sector_i : Sector
  /-- Second sector. -/
  sector_j : Sector
  /-- Numerator of coupling (scaled). -/
  numer : Nat
  /-- Denominator of coupling (scaled). -/
  denom : Nat
  /-- Denominator is positive. -/
  denom_pos : denom > 0 := by omega
  deriving Repr

/-- Coupling formula as Float. -/
def CouplingFormula.toFloat (c : CouplingFormula) : Float :=
  Float.ofNat c.numer / Float.ofNat c.denom

-- ============================================================
-- ABBREVIATIONS FOR READABILITY
-- ============================================================

-- ι = 341304, D = 1000000 (from SectorParameters)
-- (1 − ι/D) = (D − ι)/D = 658541/10⁶

/-- (D − ι) = 1000000 − 341304 = 658541. -/
private abbrev oneMinusIota : Nat := iotaD - iota   -- 658541

/-- (D + ι) = 1000000 + 341304 = 1341304. -/
private abbrev onePlusIota : Nat := iotaD + iota    -- 1341304

/-- Helper: all building blocks are positive. -/
private theorem iotaD_pos : iotaD > 0 := by simp [iotaD, iota_tau_denom]
private theorem iota_pos : iota > 0 := by simp [iota, iota_tau_numer]
private theorem oneMinusIota_pos : oneMinusIota > 0 := by
  simp [oneMinusIota, iotaD, iota, iota_tau_denom, iota_tau_numer]
private theorem onePlusIota_pos : onePlusIota > 0 := by
  simp [onePlusIota, iotaD, iota, iota_tau_denom, iota_tau_numer]

-- ============================================================
-- TEN COUPLING FORMULAS [IV.D07]
-- ============================================================

/-- κ(D,D) = 1 − ι_τ: Gravity self-coupling. -/
def kappa_DD : CouplingFormula where
  sector_i := .D
  sector_j := .D
  numer := oneMinusIota            -- 658541
  denom := iotaD                   -- 10⁶
  denom_pos := iotaD_pos

/-- κ(A,A) = ι_τ: Weak self-coupling. -/
def kappa_AA : CouplingFormula where
  sector_i := .A
  sector_j := .A
  numer := iota                    -- 341304
  denom := iotaD                   -- 10⁶
  denom_pos := iotaD_pos

/-- κ(B,B) = ι_τ²: EM self-coupling. -/
def kappa_BB : CouplingFormula where
  sector_i := .B
  sector_j := .B
  numer := iota * iota             -- 116594274681
  denom := iotaD * iotaD           -- 10¹²
  denom_pos := Nat.mul_pos iotaD_pos iotaD_pos

/-- κ(C,C) = ι_τ³/(1−ι_τ): Strong self-coupling (confinement). -/
def kappa_CC : CouplingFormula where
  sector_i := .C
  sector_j := .C
  numer := iota * iota * iota * iotaD
  denom := iotaD * iotaD * iotaD * oneMinusIota
  denom_pos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos iotaD_pos iotaD_pos) iotaD_pos) oneMinusIota_pos

/-- κ(A,B) = ι_τ³: Electroweak coupling (multiplicative closure κ(A)·κ(B)). -/
def kappa_AB : CouplingFormula where
  sector_i := .A
  sector_j := .B
  numer := iota * iota * iota            -- ι³
  denom := iotaD * iotaD * iotaD         -- D³
  denom_pos := Nat.mul_pos (Nat.mul_pos iotaD_pos iotaD_pos) iotaD_pos

/-- κ(A,C) = ι_τ⁴/(1−ι_τ): Weak-Strong coupling (multiplicative closure κ(A)·κ(C)). -/
def kappa_AC : CouplingFormula where
  sector_i := .A
  sector_j := .C
  numer := iota * iota * iota * iota * iotaD   -- ι⁴ × D (normalized)
  denom := iotaD * iotaD * iotaD * iotaD * oneMinusIota  -- D⁴ × (D−ι)
  denom_pos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos iotaD_pos iotaD_pos) iotaD_pos) iotaD_pos) oneMinusIota_pos

/-- κ(A,D) = ι_τ(1−ι_τ): Weak-Gravity coupling (temporal consistency). -/
def kappa_AD : CouplingFormula where
  sector_i := .A
  sector_j := .D
  numer := iota * oneMinusIota           -- ι × (D − ι)
  denom := iotaD * iotaD                 -- D²
  denom_pos := Nat.mul_pos iotaD_pos iotaD_pos

/-- κ(B,C) = ι_τ³/(1+ι_τ): EM-Strong = Higgs/mass crossing. -/
def kappa_BC : CouplingFormula where
  sector_i := .B
  sector_j := .C
  numer := iota * iota * iota * iotaD
  denom := iotaD * iotaD * iotaD * onePlusIota
  denom_pos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos iotaD_pos iotaD_pos) iotaD_pos) onePlusIota_pos

/-- κ(B,D) = ι_τ²(1−ι_τ): EM-Gravity (gravitational lensing). -/
def kappa_BD : CouplingFormula where
  sector_i := .B
  sector_j := .D
  numer := iota * iota * oneMinusIota                   -- ι² × (D−ι)
  denom := iotaD * iotaD * iotaD                        -- D³
  denom_pos := Nat.mul_pos (Nat.mul_pos iotaD_pos iotaD_pos) iotaD_pos

/-- κ(C,D) = ι_τ³(1−ι_τ): Strong-Gravity (mass curves time). -/
def kappa_CD : CouplingFormula where
  sector_i := .C
  sector_j := .D
  numer := iota * iota * iota * oneMinusIota  -- ι³ × (D−ι)
  denom := iotaD * iotaD * iotaD * iotaD      -- D⁴
  denom_pos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos iotaD_pos iotaD_pos) iotaD_pos) iotaD_pos

/-- The complete 10-entry coupling ledger. -/
def all_coupling_formulas : List CouplingFormula :=
  [kappa_DD, kappa_AA, kappa_BB, kappa_CC,
   kappa_AB, kappa_AC, kappa_AD,
   kappa_BC, kappa_BD, kappa_CD]

-- ============================================================
-- TEMPORAL COMPLEMENT [IV.T01]
-- ============================================================

/-- [IV.T01] κ(A;1) + κ(D;1) = 1: the temporal pair exhausts the
    depth-1 coupling budget. Gravity and Weak are complements.

    Proof: ι + (D − ι) = D, so ι/D + (D−ι)/D = 1. -/
theorem temporal_complement :
    kappa_AA.numer + kappa_DD.numer = kappa_AA.denom := by
  simp [kappa_AA, kappa_DD, iota, oneMinusIota, iotaD,
        iota_tau_numer, iota_tau_denom]

/-- The shared denominator confirms they sum to exactly 1. -/
theorem temporal_complement_denom :
    kappa_AA.denom = kappa_DD.denom := by
  simp [kappa_AA, kappa_DD]

-- ============================================================
-- TEMPORAL MULTIPLICATIVE CLOSURE [IV.T02]
-- ============================================================

/-- [IV.T02] κ(A,D) = κ(A;1) · κ(D;1): the temporal cross-coupling
    is exactly the product of the two temporal self-couplings.
    This means the temporal pair is "multiplicatively closed."

    Proof: ι(D−ι)/D² = (ι/D)·((D−ι)/D). -/
theorem temporal_multiplicative :
    kappa_AD.numer * (kappa_AA.denom * kappa_DD.denom) =
    kappa_AA.numer * kappa_DD.numer * kappa_AD.denom := by
  simp [kappa_AD, kappa_AA, kappa_DD, iota, oneMinusIota, iotaD,
        iota_tau_numer, iota_tau_denom]

-- ============================================================
-- POWER HIERARCHY [IV.P03]
-- ============================================================

/-- [IV.P03a] κ(B;2) = κ(A;1)²: EM self-coupling equals Weak squared.
    Proof: ι²/D² = (ι/D)². -/
theorem em_is_weak_squared :
    kappa_BB.numer * (kappa_AA.denom * kappa_AA.denom) =
    (kappa_AA.numer * kappa_AA.numer) * kappa_BB.denom := by
  simp [kappa_BB, kappa_AA, iota, iotaD, iota_tau_numer, iota_tau_denom]

/-- [IV.P03b] κ(A,C) = κ(A;1)·κ(C;3): Weak-Strong = Weak × Strong (multiplicative closure).
    Proof: (ι⁴·D)/(D⁴·(D−ι)) = (ι/D) · (ι³·D/(D³·(D−ι))). -/
theorem weak_strong_is_multiplicative :
    kappa_AC.numer * (kappa_AA.denom * kappa_CC.denom) =
    (kappa_AA.numer * kappa_CC.numer) * kappa_AC.denom := by
  simp [kappa_AC, kappa_AA, kappa_CC, iota, oneMinusIota, iotaD,
        iota_tau_numer, iota_tau_denom]

-- ============================================================
-- COUPLING POSITIVITY [IV.P01]
-- ============================================================

/-- [IV.P01] All 10 coupling numerators are positive.
    Since all denominators are positive by construction,
    all coupling values are strictly positive. -/
theorem all_formulas_positive :
    kappa_DD.numer > 0 ∧ kappa_AA.numer > 0 ∧
    kappa_BB.numer > 0 ∧ kappa_CC.numer > 0 ∧
    kappa_AB.numer > 0 ∧ kappa_AC.numer > 0 ∧
    kappa_AD.numer > 0 ∧ kappa_BC.numer > 0 ∧
    kappa_BD.numer > 0 ∧ kappa_CD.numer > 0 := by
  simp [kappa_DD, kappa_AA, kappa_BB, kappa_CC,
        kappa_AB, kappa_AC, kappa_AD, kappa_BC, kappa_BD, kappa_CD,
        iota, oneMinusIota, onePlusIota, iotaD,
        iota_tau_numer, iota_tau_denom]

/-- The ledger has exactly 10 entries. -/
theorem coupling_ledger_count :
    all_coupling_formulas.length = 10 := by rfl

-- ============================================================
-- COUPLING FORMULA LOOKUP
-- ============================================================

/-- Retrieve the coupling formula for a sector pair.
    Symmetric: coupling(i,j) = coupling(j,i). -/
def coupling_formula (si sj : Sector) : CouplingFormula :=
  let (a, b) := if si.toNat ≤ sj.toNat then (si, sj) else (sj, si)
  match a, b with
  | .D, .D => kappa_DD
  | .D, .A => kappa_AD
  | .D, .B => kappa_BD
  | .D, .C => kappa_CD
  | .D, .Omega => kappa_DD   -- D-ω coupling defaults to D self-coupling
  | .A, .A => kappa_AA
  | .A, .B => kappa_AB
  | .A, .C => kappa_AC
  | .A, .Omega => kappa_AA   -- A-ω defaults to A self-coupling
  | .B, .B => kappa_BB
  | .B, .C => kappa_BC
  | .B, .Omega => kappa_BC   -- B-ω = B-C (ω = B∩C)
  | .C, .C => kappa_CC
  | .C, .Omega => kappa_BC   -- C-ω = B-C
  | .Omega, .Omega => kappa_BC  -- ω self-coupling = B-C crossing
  | _, _ => kappa_DD            -- unreachable: ordering guarantees a ≤ b

-- ============================================================
-- ORDERING VERIFICATION
-- ============================================================

/-- Self-couplings are ordered: κ(C) < κ(B) < κ(A) < κ(D).
    Strong < EM < Weak < Gravity in coupling strength. -/
theorem self_coupling_order :
    kappa_CC.toFloat < kappa_BB.toFloat ∧
    kappa_BB.toFloat < kappa_AA.toFloat ∧
    kappa_AA.toFloat < kappa_DD.toFloat := by
  simp [CouplingFormula.toFloat, kappa_CC, kappa_BB, kappa_AA, kappa_DD,
        iota, oneMinusIota, iotaD, iota_tau_numer, iota_tau_denom]
  native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Self-couplings
#eval kappa_DD.toFloat   -- ≈ 0.6585 (gravity)
#eval kappa_AA.toFloat   -- ≈ 0.3415 (weak = ι_τ)
#eval kappa_BB.toFloat   -- ≈ 0.1166 (EM = ι_τ²)
#eval kappa_CC.toFloat   -- ≈ 0.0604 (strong)

-- Cross-couplings
#eval kappa_AB.toFloat   -- ≈ 0.0398 (electroweak = ι³)
#eval kappa_AC.toFloat   -- ≈ 0.0206 (weak-strong = ι⁴/(1−ι))
#eval kappa_AD.toFloat   -- ≈ 0.2249 (weak-gravity)
#eval kappa_BC.toFloat   -- ≈ 0.0297 (higgs/mass)
#eval kappa_BD.toFloat   -- ≈ 0.0767 (EM-gravity)
#eval kappa_CD.toFloat   -- ≈ 0.0262 (strong-gravity)

-- Temporal complement check
#eval kappa_AA.numer + kappa_DD.numer  -- 1000000
#eval kappa_AA.denom                    -- 1000000

-- 10 entries
#eval all_coupling_formulas.length      -- 10

end Tau.BookIV.Sectors

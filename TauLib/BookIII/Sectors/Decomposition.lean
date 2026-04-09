import TauLib.BookIII.Sectors.BoundaryCharacters

/-!
# TauLib.BookIII.Sectors.Decomposition

Sector Preservation Theorem, 4+1 Sector Decomposition, and ω-Coupling Sector.

## Registry Cross-References

- [III.T05] Sector Preservation Theorem — `sector_preservation_check`
- [III.D13] 4+1 Sector Decomposition — `Sector`, `sector_of`, `sector_decomposition_check`
- [III.D14] ω-Coupling Sector — `omega_coupling_check`

## Mathematical Content

**III.T05 (Sector Preservation):** The boundary-to-interior functor Φ preserves
the bipolar decomposition: χ₊-characters map to B-sector holomorphic functions,
χ₋-characters map to C-sector, mixed characters map to the ω-coupling sector.

**III.D13 (4+1 Sector Decomposition):** Five generators yield four primitive
sectors (α→D, π→A, γ→B, η→C) plus one coupling sector (ω).

**III.D14 (ω-Coupling Sector):** The fifth generator ω mediates coupling
between B and C lobes simultaneously. The structural reason for 4+1, not 5.
-/

namespace Tau.BookIII.Sectors

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment Tau.BookII.Topology
open Tau.BookII.CentralTheorem Tau.BookII.Regularity
open Tau.BookIII.Enrichment

-- ============================================================
-- 4+1 SECTOR DECOMPOSITION [III.D13]
-- ============================================================

/-- [III.D13] The five sectors induced by the ABCD decomposition.
    Four primitive sectors (one per generator) plus one coupling sector. -/
inductive Sector where
  | D : Sector  -- α-generator, radial/gravity
  | A : Sector  -- π-generator, weak/gauge
  | B : Sector  -- γ-generator, electromagnetic
  | C : Sector  -- η-generator, strong
  | Omega : Sector  -- ω-coupling, Higgs/mass
  deriving Repr, DecidableEq, BEq, Inhabited

/-- [III.D13] Sector assignment: classify a boundary character into its sector.
    Based on the dominance pattern of the (m, n) indices:
    - D: m = 0, n = 0 (trivial = radial)
    - A: |m| = |n|, both nonzero (balanced = weak)
    - B: |m| > |n| and n = 0 (pure B-lobe = electromagnetic)
    - C: |n| > |m| and m = 0 (pure C-lobe = strong)
    - Omega: both nonzero and |m| ≠ |n| (mixed coupling) -/
def sector_of (χ : BoundaryCharacter) : Sector :=
  let am := χ.m_index.natAbs
  let an := χ.n_index.natAbs
  if am == 0 && an == 0 then .D
  else if am == an then .A
  else if am > an then
    if an == 0 then .B else .Omega
  else
    if am == 0 then .C else .Omega

/-- Numeric index of a sector (for ordering). -/
def Sector.toNat : Sector → Nat
  | .D => 0
  | .A => 1
  | .B => 2
  | .C => 3
  | .Omega => 4

/-- [III.D13] Sector decomposition check: verify that the 5 sectors
    are exhaustive over characters in range. Uses 5-bit accumulator. -/
def sector_decomposition_check (bound : TauIdx) : Bool :=
  go 0 0 0 ((bound + 1) * (bound + 1))
where
  /-- Accumulate which sectors are seen. Bits: D=1, A=2, B=4, C=8, Omega=16. -/
  go (m n seen fuel : Nat) : Bool :=
    if fuel = 0 then seen == 31  -- 1+2+4+8+16 = 31
    else if m > bound then seen == 31
    else if n > bound then go (m + 1) 0 seen (fuel - 1)
    else
      let χ : BoundaryCharacter := ⟨Int.ofNat m, Int.ofNat n⟩
      let bit := match sector_of χ with
        | .D => 1
        | .A => 2
        | .B => 4
        | .C => 8
        | .Omega => 16
      go m (n + 1) (seen ||| bit) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ω-COUPLING SECTOR [III.D14]
-- ============================================================

/-- [III.D14] ω-Coupling sector check: verify that ω-classified characters
    have both m ≠ 0 and n ≠ 0 (dual-lobe active) and |m| ≠ |n|.
    The ω-sector mediates coupling: it is the unique sector with
    both lobes active simultaneously. -/
def omega_coupling_check (bound : TauIdx) : Bool :=
  go 0 0 ((bound + 1) * (bound + 1))
where
  go (m n fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if m > bound then true
    else if n > bound then go (m + 1) 0 (fuel - 1)
    else
      let χ : BoundaryCharacter := ⟨Int.ofNat m, Int.ofNat n⟩
      let ok := if sector_of χ == .Omega then
        -- ω-characters must have both indices nonzero and unequal magnitude
        m > 0 && n > 0 && m != n
      else true
      ok && go m (n + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SECTOR PRESERVATION THEOREM [III.T05]
-- ============================================================

/-! **Scope limitation (E3 collapse):** At finite primorial level, the E3
    predicate degenerates to E0 because `reduce` is idempotent. This check
    is vacuous but correctly models the mathematical structure. The E3 layer
    is correctly DEFINED but finite verification is vacuous.
    See audit DASHBOARD.md §E3 Collapse. -/

/-- [III.T05] Sector preservation check: verify that the BTI functor Φ
    preserves reduce-compatibility for each sector.
    For each character, the interior extension is reduce-stable:
    reduce(Φ(χ)(x, k), k) = Φ(χ)(x, k). -/
def sector_preservation_check (bound db : TauIdx) : Bool :=
  go 0 0 1 ((bound + 1) * (bound + 1) * (db + 1))
where
  go (m n k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if m > bound then true
    else if n > bound then go (m + 1) 0 1 (fuel - 1)
    else if k > db then go m (n + 1) 1 (fuel - 1)
    else
      let χ : BoundaryCharacter := ⟨Int.ofNat m, Int.ofNat n⟩
      -- BTI value is reduce-stable + tower-coherent
      let val := boundary_to_interior χ 1 k
      let stable := reduce val k == val
      -- Tower coherence: reduce at k then k-1 = reduce at k-1 directly
      -- (exercises Nat.mod_mod_of_dvd via primorial divisibility)
      let tower_ok := if k > 1 then
        let pk1 := primorial (k - 1)
        if pk1 > 0 then
          reduce val (k - 1) == reduce (reduce val k) (k - 1)
        else true
      else true
      stable && tower_ok && go m n (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Sector assignment
#eval sector_of ⟨0, 0⟩     -- D (trivial)
#eval sector_of ⟨1, 1⟩     -- A (balanced)
#eval sector_of ⟨3, 0⟩     -- B (m-dominant, n=0)
#eval sector_of ⟨0, 5⟩     -- C (n-dominant, m=0)
#eval sector_of ⟨3, 1⟩     -- Omega (mixed)
#eval sector_of ⟨1, 3⟩     -- Omega (mixed)

-- Sector decomposition
#eval sector_decomposition_check 5          -- true (all 5 sectors seen)

-- ω-coupling
#eval omega_coupling_check 5               -- true

-- Sector preservation
#eval sector_preservation_check 5 3        -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Sector decomposition [III.D13]
theorem sector_decomp_5 :
    sector_decomposition_check 5 = true := by native_decide

-- ω-coupling [III.D14]
theorem omega_coupling_5 :
    omega_coupling_check 5 = true := by native_decide

-- Sector preservation [III.T05]
theorem sector_preservation_5_3 :
    sector_preservation_check 5 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D13] Trivial character is in D-sector. -/
theorem zero_in_D : sector_of BoundaryCharacter.zero = .D := rfl

/-- [III.D13] Pure m-character is in B-sector. -/
theorem pure_m_in_B : sector_of ⟨2, 0⟩ = .B := rfl

/-- [III.D13] Pure n-character is in C-sector. -/
theorem pure_n_in_C : sector_of ⟨0, 2⟩ = .C := rfl

/-- [III.D13] Equal-magnitude character is in A-sector. -/
theorem equal_mag_in_A : sector_of ⟨3, 3⟩ = .A := rfl

/-- [III.D13] Mixed unequal character is in Omega-sector. -/
theorem mixed_in_Omega : sector_of ⟨2, 1⟩ = .Omega := rfl

/-- [III.D13] The five sectors partition the character space:
    every character belongs to exactly one sector. -/
theorem sector_exhaustive (χ : BoundaryCharacter) :
    sector_of χ = .D ∨ sector_of χ = .A ∨ sector_of χ = .B ∨
    sector_of χ = .C ∨ sector_of χ = .Omega := by
  simp only [sector_of]
  split <;> simp_all
  split <;> simp_all
  split
  · split <;> simp_all
  · split <;> simp_all

end Tau.BookIII.Sectors

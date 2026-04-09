import TauLib.BookII.Transcendentals.EEarned
import TauLib.BookII.Interior.BipolarDecomposition
import TauLib.BookI.Boundary.SplitComplex

/-!
# TauLib.BookII.Transcendentals.JReplacesI

j replaces i: the split-complex unit j (j^2 = +1) replaces the
imaginary unit i (i^2 = -1) as the fundamental algebraic unit.

## Registry Cross-References

- [II.D32] Interior j-Unit — `j_unit`, `j_squared_check`
- [II.D33] Bipolar Idempotents Interior — `idempotent_check`
- [II.T24] j Replaces i — `j_vs_i_check`

## Mathematical Content

The split-complex unit j with j^2 = +1 forces hyperbolic (wave) geometry
rather than elliptic (Laplacian) geometry. The idempotents e_+ = (1+j)/2
and e_- = (1-j)/2 provide the bipolar decomposition.

Key contrast:
- i^2 = -1 (Gaussian): rotation, elliptic PDE, NO nontrivial idempotents over Z
- j^2 = +1 (split-complex): polarity, wave PDE, idempotents e_+, e_-

The split-complex structure is FORCED by the bipolar prime partition (I.T10).
This module verifies the algebraic properties at the interior level.
-/

namespace Tau.BookII.Transcendentals

open Tau.BookII.Interior Tau.BookII.Domains
open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation

-- ============================================================
-- j-UNIT [II.D32]
-- ============================================================

/-- [II.D32] The interior j-unit: j = (0, 1) in SplitComplex. -/
def j_unit : SplitComplex := ⟨0, 1⟩

/-- j^2 = 1: the defining property. (0,1)*(0,1) = (0*0+1*1, 0*1+1*0) = (1,0). -/
def j_squared_check : Bool :=
  SplitComplex.mul j_unit j_unit == ⟨1, 0⟩

/-- j is not trivial: j != 0 and j != 1. -/
def j_nontrivial_check : Bool :=
  j_unit != SplitComplex.zero && j_unit != SplitComplex.one

/-- Polarity involution: sigma(j) = -j. -/
def j_involution_check : Bool :=
  polarity_inv j_unit == SplitComplex.neg j_unit

-- ============================================================
-- BIPOLAR IDEMPOTENTS [II.D33]
-- ============================================================

/-- [II.D33] Bipolar idempotents in sector coordinates.
    e_+ = (1, 0) and e_- = (0, 1) in SectorPair.

    Algebraic properties:
    1. e_+^2 = e_+ (idempotent)
    2. e_-^2 = e_- (idempotent)
    3. e_+ * e_- = 0 (orthogonal)
    4. e_+ + e_- = (1,1) = unity -/
def idempotent_check : Bool :=
  -- e_+ idempotent
  SectorPair.mul e_plus_sector e_plus_sector == e_plus_sector &&
  -- e_- idempotent
  SectorPair.mul e_minus_sector e_minus_sector == e_minus_sector &&
  -- Orthogonality
  SectorPair.mul e_plus_sector e_minus_sector == ⟨0, 0⟩ &&
  -- Partition of unity
  SectorPair.add e_plus_sector e_minus_sector == ⟨1, 1⟩

/-- Interior projection: idempotent action on interior bipolar pairs.
    e_+ * (b, c) = (b, 0): keeps B-sector, kills C-sector.
    e_- * (b, c) = (0, c): kills B-sector, keeps C-sector. -/
def interior_projection_check : Bool :=
  -- e_+ * (3, 2) = (3, 0)
  SectorPair.mul e_plus_sector ⟨3, 2⟩ == ⟨3, 0⟩ &&
  -- e_- * (3, 2) = (0, 2)
  SectorPair.mul e_minus_sector ⟨3, 2⟩ == ⟨0, 2⟩ &&
  -- Sum recovers original: (3, 0) + (0, 2) = (3, 2)
  SectorPair.add (SectorPair.mul e_plus_sector ⟨3, 2⟩)
                 (SectorPair.mul e_minus_sector ⟨3, 2⟩) == ⟨3, 2⟩

-- ============================================================
-- j REPLACES i [II.T24]
-- ============================================================

/-- [II.T24] j replaces i: comprehensive comparison.

    1. j^2 = +1 (split-complex, hyperbolic)
    2. i^2 = -1 (Gaussian, elliptic)
    3. j admits nontrivial idempotents; i does not (I.T10)
    4. Zero divisors in H_tau witness polarity structure

    The wave equation u_tt = u_xx comes from j^2 = +1.
    The Laplace equation u_tt + u_xx = 0 would come from i^2 = -1.
    Category tau chooses j (waves, polarity) over i (rotation). -/
def j_vs_i_check : Bool :=
  -- j^2 = +1 (split-complex)
  SplitComplex.mul ⟨0, 1⟩ ⟨0, 1⟩ == ⟨1, 0⟩ &&
  -- i^2 = -1 (Gaussian): (0,1)*(0,1) = (0*0 - 1*1, 0*1 + 1*0) = (-1, 0)
  GaussInt.mul ⟨0, 1⟩ ⟨0, 1⟩ == ⟨-1, 0⟩ &&
  -- j has nontrivial idempotents
  idempotent_check &&
  -- Zero divisors exist: (1+j)(1-j) = 0
  SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩ == SplitComplex.zero

/-- Wave vs Laplace: the two signatures in sector coordinates.
    j^2 = +1: sector product is componentwise (wave eq characteristic coords)
    i^2 = -1: Gaussian product mixes components (elliptic) -/
def wave_vs_laplace_check : Bool :=
  -- Split-complex sector product: componentwise
  let sp1 : SectorPair := to_sectors ⟨2, 3⟩  -- (5, -1)
  let sp2 : SectorPair := to_sectors ⟨1, 4⟩  -- (5, -3)
  let sp_prod := SectorPair.mul sp1 sp2       -- (25, 3)
  -- Verify it equals to_sectors of the split-complex product
  let sc_prod := SplitComplex.mul ⟨2, 3⟩ ⟨1, 4⟩  -- (2*1+3*4, 2*4+3*1) = (14, 11)
  sp_prod == to_sectors sc_prod

-- ============================================================
-- INTERIOR BIPOLAR INHERITANCE
-- ============================================================

/-- Every tau-admissible point inherits bipolar decomposition via j.
    The B-coordinate maps to the e_+-sector, C to e_-. -/
def interior_bipolar_via_j (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let bp := interior_bipolar p
      -- e_+ projection recovers B-sector
      let proj_plus := SectorPair.mul e_plus_sector bp
      let proj_minus := SectorPair.mul e_minus_sector bp
      -- Sum recovers full bipolar pair
      (SectorPair.add proj_plus proj_minus == bp) &&
      go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- j-unit
#eval j_unit                           -- (0, 1)
#eval SplitComplex.mul j_unit j_unit   -- (1, 0) = j^2 = 1
#eval j_squared_check                  -- true
#eval j_nontrivial_check               -- true
#eval j_involution_check               -- true

-- Idempotents
#eval idempotent_check                 -- true
#eval interior_projection_check        -- true

-- j vs i
#eval j_vs_i_check                     -- true
#eval wave_vs_laplace_check            -- true

-- Interior bipolar
#eval interior_bipolar_via_j 30        -- true

-- Formal verification
theorem j_sq : j_squared_check = true := by native_decide
theorem j_nontriv : j_nontrivial_check = true := by native_decide
theorem j_invol : j_involution_check = true := by native_decide
theorem idemp : idempotent_check = true := by native_decide
theorem int_proj : interior_projection_check = true := by native_decide
theorem j_vs_i : j_vs_i_check = true := by native_decide
theorem wave_laplace : wave_vs_laplace_check = true := by native_decide
theorem int_bipolar_30 : interior_bipolar_via_j 30 = true := by native_decide

end Tau.BookII.Transcendentals

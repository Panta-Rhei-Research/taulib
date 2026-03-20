import TauLib.BookII.Hartogs.SheafCoherence

/-!
# TauLib.BookII.Regularity.IdempotentDecomposition

Idempotent decomposition of tau-holomorphic functions into B-channel
and C-channel components via the canonical idempotents e₊, e₋.

## Registry Cross-References

- [II.L07] Idempotent Decomposition Lemma — `decompose_recovery_check`
- [II.D48] Canonical Decomposition — `idempotent_decompose`
- [II.P10] Decomposition Functoriality — `decompose_functorial_check`

## Mathematical Content

Every tau-holomorphic function f decomposes uniquely as
  f = e₊ · f₊ + e₋ · f₋
where f₊(x) = e₊ · f(x) keeps the B-channel and f₋(x) = e₋ · f(x)
keeps the C-channel.

In sector coordinates (where multiplication is componentwise):
- e₊ = (1, 0) projects onto the B-sector
- e₋ = (0, 1) projects onto the C-sector

Key properties:
- **Recovery (II.L07):** proj_plus(f(x)) + proj_minus(f(x)) = f(x)
- **Orthogonality:** proj_plus * proj_minus = 0
- **Idempotency:** proj_plus² = proj_plus, proj_minus² = proj_minus
- **Functoriality (II.P10):** decomposition commutes with hol_compose

These follow from the sector-coordinate representation of SectorPair,
where mul and add are both componentwise.
-/

namespace Tau.BookII.Regularity

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.BookII.Hartogs Tau.Holomorphy

-- ============================================================
-- IDEMPOTENT DECOMPOSITION [II.D48]
-- ============================================================

/-- [II.D48] Idempotent decomposition of a SectorPair into
    B-channel and C-channel components.

    Given bp = (B, C), returns:
    - fst = e₊ · bp = (1,0) * (B,C) = (B, 0)   [B-channel]
    - snd = e₋ · bp = (0,1) * (B,C) = (0, C)   [C-channel]

    The decomposition is canonical: determined entirely by the
    idempotent structure of the sector algebra. -/
def idempotent_decompose (bp : SectorPair) : SectorPair × SectorPair :=
  (SectorPair.mul e_plus_sector bp, SectorPair.mul e_minus_sector bp)

/-- B-channel projection: keeps only the B-sector component. -/
def proj_plus (bp : SectorPair) : SectorPair :=
  SectorPair.mul e_plus_sector bp

/-- C-channel projection: keeps only the C-sector component. -/
def proj_minus (bp : SectorPair) : SectorPair :=
  SectorPair.mul e_minus_sector bp

-- ============================================================
-- PROJECTION STRUCTURE [II.D48]
-- ============================================================

/-- proj_plus kills the C-channel: the C-sector of e₊ · bp is always 0. -/
theorem proj_plus_kills_c (bp : SectorPair) :
    (proj_plus bp).c_sector = 0 := by
  simp [proj_plus, SectorPair.mul, e_plus_sector]

/-- proj_minus kills the B-channel: the B-sector of e₋ · bp is always 0. -/
theorem proj_minus_kills_b (bp : SectorPair) :
    (proj_minus bp).b_sector = 0 := by
  simp [proj_minus, SectorPair.mul, e_minus_sector]

/-- proj_plus preserves the B-channel: the B-sector of e₊ · bp equals bp.b. -/
theorem proj_plus_preserves_b (bp : SectorPair) :
    (proj_plus bp).b_sector = bp.b_sector := by
  simp [proj_plus, SectorPair.mul, e_plus_sector]

/-- proj_minus preserves the C-channel: the C-sector of e₋ · bp equals bp.c. -/
theorem proj_minus_preserves_c (bp : SectorPair) :
    (proj_minus bp).c_sector = bp.c_sector := by
  simp [proj_minus, SectorPair.mul, e_minus_sector]

-- ============================================================
-- IDEMPOTENT DECOMPOSITION LEMMA [II.L07]
-- ============================================================

/-- [II.L07] Idempotent Decomposition Lemma (formal):
    e₊ · bp + e₋ · bp = bp for all sector pairs bp.

    This is the fundamental decomposition: every element of the
    bipolar spectral algebra decomposes uniquely into B-channel
    and C-channel components, and the sum recovers the original. -/
theorem decompose_recovery (bp : SectorPair) :
    SectorPair.add (proj_plus bp) (proj_minus bp) = bp := by
  simp [proj_plus, proj_minus, SectorPair.add, SectorPair.mul,
        e_plus_sector, e_minus_sector]

/-- Orthogonality: proj_plus(bp) * proj_minus(bp) = (0, 0).
    The B-channel and C-channel carry independent information. -/
theorem proj_orthogonal (bp : SectorPair) :
    SectorPair.mul (proj_plus bp) (proj_minus bp) = ⟨0, 0⟩ := by
  simp [proj_plus, proj_minus, SectorPair.mul, e_plus_sector, e_minus_sector]

/-- Idempotency of proj_plus: projecting twice is the same as projecting once. -/
theorem proj_plus_idem (bp : SectorPair) :
    proj_plus (proj_plus bp) = proj_plus bp := by
  simp [proj_plus, SectorPair.mul, e_plus_sector]

/-- Idempotency of proj_minus: projecting twice is the same as projecting once. -/
theorem proj_minus_idem (bp : SectorPair) :
    proj_minus (proj_minus bp) = proj_minus bp := by
  simp [proj_minus, SectorPair.mul, e_minus_sector]

-- ============================================================
-- DECOMPOSITION RECOVERY CHECK (computational) [II.L07]
-- ============================================================

/-- [II.L07] Computational check: e₊ · bp + e₋ · bp = bp
    for all tau-admissible points in [2, bound]. -/
def decompose_recovery_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let bp := interior_bipolar p
      let (fp, fm) := idempotent_decompose bp
      -- Recovery: fp + fm = bp
      let recovery := SectorPair.add fp fm == bp
      -- Orthogonality: fp * fm = 0
      let ortho := SectorPair.mul fp fm == ⟨0, 0⟩
      -- Structure: fp has zero C, fm has zero B
      let struct := fp.c_sector == 0 && fm.b_sector == 0
      -- Preservation: fp.B = bp.B and fm.C = bp.C
      let pres := fp.b_sector == bp.b_sector && fm.c_sector == bp.c_sector
      recovery && ortho && struct && pres &&
      go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- DECOMPOSITION OF STAGEFUN [II.D48]
-- ============================================================

/-- [II.D48] Decompose a StageFun into its B-channel and C-channel
    components. The B-channel component has c_fun = 0, the C-channel
    component has b_fun = 0.

    This is the stagewise lift of the idempotent decomposition. -/
def stagefun_decompose (sf : StageFun) : StageFun × StageFun :=
  -- B-channel: keep b_fun, zero out c_fun
  let b_part : StageFun := ⟨sf.b_fun, fun _ _ => 0⟩
  -- C-channel: zero out b_fun, keep c_fun
  let c_part : StageFun := ⟨fun _ _ => 0, sf.c_fun⟩
  (b_part, c_part)

/-- Stagewise decomposition recovery check: the B-part and C-part
    of a StageFun, evaluated and combined as SectorPairs, recover
    the original StageFun evaluation. -/
def stagefun_decompose_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let sf := id_stage
      let (bp, cp) := stagefun_decompose sf
      -- B-part evaluation
      let b_val : SectorPair := ⟨bp.b_fun x k, bp.c_fun x k⟩
      -- C-part evaluation
      let c_val : SectorPair := ⟨cp.b_fun x k, cp.c_fun x k⟩
      -- Original evaluation
      let orig : SectorPair := ⟨sf.b_fun x k, sf.c_fun x k⟩
      -- Recovery: b_val + c_val = orig
      let ok := SectorPair.add b_val c_val == orig
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- DECOMPOSITION FUNCTORIALITY [II.P10]
-- ============================================================

/-- [II.P10] Decomposition functoriality check:
    the idempotent decomposition commutes with holomorphic composition.

    For endomorphisms f, g on the primorial tower:
    proj_plus(f . g) = proj_plus(f) . proj_plus(g)
    proj_minus(f . g) = proj_minus(f) . proj_minus(g)

    In the stagefun setting, this means the B-channel of a composition
    equals the composition of B-channels, and similarly for C-channels. -/
def decompose_functorial_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- Use chi_plus_stage and id_stage as test endomorphisms
      let f := chi_plus_stage
      let g := id_stage
      -- Compose, then decompose
      let comp := StageFun.comp f g
      let (comp_b, comp_c) := stagefun_decompose comp
      -- Decompose, then compose
      let (f_b, f_c) := stagefun_decompose f
      let (g_b, g_c) := stagefun_decompose g
      let b_comp := StageFun.comp f_b g_b
      let c_comp := StageFun.comp f_c g_c
      -- B-channels match
      let b_ok := comp_b.b_fun x k == b_comp.b_fun x k
      -- C-channels match
      let c_ok := comp_c.c_fun x k == c_comp.c_fun x k
      b_ok && c_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.P10] Extended functoriality: test with multiple endomorphism pairs. -/
def decompose_functorial_extended (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- Test pair 1: chi_minus and id
      let f1 := chi_minus_stage
      let g1 := id_stage
      let comp1 := StageFun.comp f1 g1
      let (comp1_b, comp1_c) := stagefun_decompose comp1
      let (f1_b, f1_c) := stagefun_decompose f1
      let (g1_b, g1_c) := stagefun_decompose g1
      let ok1 := comp1_b.b_fun x k == (StageFun.comp f1_b g1_b).b_fun x k &&
                 comp1_c.c_fun x k == (StageFun.comp f1_c g1_c).c_fun x k
      -- Test pair 2: id and chi_plus
      let f2 := id_stage
      let g2 := chi_plus_stage
      let comp2 := StageFun.comp f2 g2
      let (comp2_b, comp2_c) := stagefun_decompose comp2
      let (f2_b, f2_c) := stagefun_decompose f2
      let (g2_b, g2_c) := stagefun_decompose g2
      let ok2 := comp2_b.b_fun x k == (StageFun.comp f2_b g2_b).b_fun x k &&
                 comp2_c.c_fun x k == (StageFun.comp f2_c g2_c).c_fun x k
      ok1 && ok2 && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL IDEMPOTENT DECOMPOSITION CHECK
-- ============================================================

/-- [II.L07 + II.D48 + II.P10] Complete idempotent decomposition verification. -/
def full_idempotent_check (bound db : TauIdx) : Bool :=
  decompose_recovery_check bound &&
  stagefun_decompose_check bound db &&
  decompose_functorial_check bound db &&
  decompose_functorial_extended bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Idempotent decomposition
#eval idempotent_decompose ⟨3, 2⟩        -- ((3, 0), (0, 2))
#eval idempotent_decompose ⟨5, 7⟩        -- ((5, 0), (0, 7))
#eval idempotent_decompose ⟨0, 0⟩        -- ((0, 0), (0, 0))

-- Projections
#eval proj_plus ⟨3, 2⟩                   -- (3, 0)
#eval proj_minus ⟨3, 2⟩                  -- (0, 2)

-- Recovery
#eval SectorPair.add (proj_plus ⟨3, 2⟩) (proj_minus ⟨3, 2⟩)   -- (3, 2)

-- Orthogonality
#eval SectorPair.mul (proj_plus ⟨3, 2⟩) (proj_minus ⟨3, 2⟩)   -- (0, 0)

-- Decompose on tau-admissible points
#eval let p := from_tau_idx 64; idempotent_decompose (interior_bipolar p)
  -- from_tau_idx 64 = (2,3,2,1), interior = (3,2), decompose = ((3,0),(0,2))

-- Recovery check
#eval decompose_recovery_check 30        -- true

-- Stagefun decomposition
#eval stagefun_decompose_check 12 4      -- true

-- Functoriality
#eval decompose_functorial_check 12 4    -- true
#eval decompose_functorial_extended 12 4 -- true

-- Full check
#eval full_idempotent_check 12 4         -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Recovery [II.L07]
theorem recovery_30 :
    decompose_recovery_check 30 = true := by native_decide

-- Stagefun decomposition [II.D48]
theorem stagefun_decompose_12_4 :
    stagefun_decompose_check 12 4 = true := by native_decide

-- Functoriality [II.P10]
theorem functorial_12_4 :
    decompose_functorial_check 12 4 = true := by native_decide

theorem functorial_ext_12_4 :
    decompose_functorial_extended 12 4 = true := by native_decide

-- Full check
theorem full_idempotent_12_4 :
    full_idempotent_check 12 4 = true := by native_decide

end Tau.BookII.Regularity

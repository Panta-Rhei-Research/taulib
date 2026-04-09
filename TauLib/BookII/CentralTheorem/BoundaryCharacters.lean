import TauLib.BookII.Enrichment.EnrichmentLadder

/-!
# TauLib.BookII.CentralTheorem.BoundaryCharacters

Idempotent-supported boundary characters and the character algebra ring structure.

## Registry Cross-References

- [II.D59] Idempotent-Supported Character — `IdempotentCharacter`, `idemp_character_check`
- [II.P14] Character Algebra Ring Structure — `character_add_check`, `character_mul_check`

## Mathematical Content

A boundary character chi : Z-hat_tau -> H_tau is **idempotent-supported** if
chi = e_plus * chi_plus + e_minus * chi_minus. Every spectral character valued
in calibrated H_tau admits this unique decomposition.

In the sector-pair model, an idempotent-supported character at stage k on
input x is a SectorPair (B-component, C-component). The character is
determined by its B-channel and C-channel projections:

  e_plus * (B, C) = (B, 0)   -- B-channel
  e_minus * (B, C) = (0, C)  -- C-channel

The decomposition is unique because e_plus + e_minus = (1, 1) and
e_plus * e_minus = (0, 0).

**Character tower coherence**: reduce(chi(x, k+1), k) = chi(x, k).
This connects boundary characters to the primorial inverse system.

**Character algebra (II.P14)**: The set of idempotent-supported characters
forms a ring under pointwise operations. Addition and multiplication of
characters preserve idempotent support because the sector algebra is
closed under componentwise addition and multiplication.
-/

namespace Tau.BookII.CentralTheorem

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy
open Tau.BookII.Hartogs Tau.BookII.Regularity Tau.BookII.Enrichment

-- ============================================================
-- IDEMPOTENT-SUPPORTED CHARACTER [II.D59]
-- ============================================================

/-- [II.D59] An idempotent-supported character is a stagewise map
    from (x, k) to a SectorPair, representing the B-channel and
    C-channel components. The character is determined by its
    idempotent projections: chi = e_plus * chi_plus + e_minus * chi_minus.

    In the primorial model, the character at stage k on input x is:
    - B-component: the B-coordinate of from_tau_idx(reduce(x, k))
    - C-component: the C-coordinate of from_tau_idx(reduce(x, k))

    This is the canonical character associated to x. -/
structure IdempotentCharacter where
  /-- B-channel function: (x, k) -> B-component at stage k. -/
  b_ch : TauIdx -> TauIdx -> Int
  /-- C-channel function: (x, k) -> C-component at stage k. -/
  c_ch : TauIdx -> TauIdx -> Int
  deriving Inhabited

/-- Evaluate an idempotent character at (x, k) as a SectorPair. -/
def IdempotentCharacter.eval (chi : IdempotentCharacter) (x k : TauIdx) : SectorPair :=
  { b_sector := chi.b_ch x k, c_sector := chi.c_ch x k }

/-- The canonical idempotent character: read off B and C from the ABCD chart
    of the stage-k reduction. -/
def canonical_character : IdempotentCharacter :=
  { b_ch := fun x k => (from_tau_idx (reduce x k)).b
  , c_ch := fun x k => (from_tau_idx (reduce x k)).c }

/-- The chi_plus character: B-channel only. -/
def chi_plus_character : IdempotentCharacter :=
  { b_ch := fun x k => (reduce x k : Int)
  , c_ch := fun _ _ => 0 }

/-- The chi_minus character: C-channel only. -/
def chi_minus_character : IdempotentCharacter :=
  { b_ch := fun _ _ => 0
  , c_ch := fun x k => (reduce x k : Int) }

-- ============================================================
-- IDEMPOTENT DECOMPOSITION CHECK [II.D59]
-- ============================================================

/-- [II.D59] Idempotent decomposition check: for each x at stage k,
    the character value (B, C) satisfies
    e_plus * (B, C) + e_minus * (B, C) = (B, C).

    This verifies that the character IS its own idempotent decomposition:
    the B-channel and C-channel projections sum to the full character. -/
def idemp_character_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let chi := canonical_character.eval x k
      -- e_plus * chi = (B, 0)
      let proj_plus := SectorPair.mul e_plus_sector chi
      -- e_minus * chi = (0, C)
      let proj_minus := SectorPair.mul e_minus_sector chi
      -- e_plus * chi + e_minus * chi = chi
      let recovery := SectorPair.add proj_plus proj_minus == chi
      -- B-channel projection has zero C
      let b_ok := proj_plus.c_sector == 0
      -- C-channel projection has zero B
      let c_ok := proj_minus.b_sector == 0
      recovery && b_ok && c_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CHARACTER TOWER COHERENCE [II.D59]
-- ============================================================

/-- Character tower coherence: reduce(chi(x, k+1), k) = chi(x, k).
    For the canonical character, this means:
    - B: the B-coordinate of from_tau_idx(reduce(reduce(x, k+1), k))
      equals the B-coordinate of from_tau_idx(reduce(x, k))
    - C: similarly for the C-coordinate

    Since reduce(reduce(x, k+1), k) = reduce(x, k) by reduction_compat,
    the same input to from_tau_idx yields the same ABCD chart. -/
def character_tower_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go (x + 1) 1 (fuel - 1)
    else
      -- The tower coherence means: the character at the reduced stage
      -- is determined by the reduction. Concretely, verify that the
      -- stage-k character equals the character computed from the
      -- stage-(k+1) reduction projected down.
      let reduced_x := reduce (reduce x (k + 1)) k
      let direct_x := reduce x k
      let tower_ok := reduced_x == direct_x
      -- If the inputs to from_tau_idx are equal, outputs are equal
      tower_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CHARACTER ALGEBRA: ADDITION [II.P14]
-- ============================================================

/-- Add two idempotent characters pointwise. -/
def IdempotentCharacter.add (chi1 chi2 : IdempotentCharacter) : IdempotentCharacter :=
  { b_ch := fun x k => chi1.b_ch x k + chi2.b_ch x k
  , c_ch := fun x k => chi1.c_ch x k + chi2.c_ch x k }

/-- [II.P14] Character addition preserves idempotent support:
    if chi1 and chi2 are idempotent-supported, then chi1 + chi2 is also
    idempotent-supported.

    Proof: e_plus * (B1+B2, C1+C2) = (B1+B2, 0) and
    e_minus * (B1+B2, C1+C2) = (0, C1+C2), and their sum
    = (B1+B2, C1+C2) = (chi1 + chi2). -/
def character_add_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- Sum of canonical and chi_plus characters
      let sum_char := IdempotentCharacter.add canonical_character chi_plus_character
      let sum_val := sum_char.eval x k
      -- Check idempotent support of the sum
      let proj_plus := SectorPair.mul e_plus_sector sum_val
      let proj_minus := SectorPair.mul e_minus_sector sum_val
      let recovery := SectorPair.add proj_plus proj_minus == sum_val
      let b_ok := proj_plus.c_sector == 0
      let c_ok := proj_minus.b_sector == 0
      recovery && b_ok && c_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CHARACTER ALGEBRA: MULTIPLICATION [II.P14]
-- ============================================================

/-- Multiply two idempotent characters pointwise (using SectorPair.mul). -/
def IdempotentCharacter.mul (chi1 chi2 : IdempotentCharacter) : IdempotentCharacter :=
  { b_ch := fun x k => chi1.b_ch x k * chi2.b_ch x k
  , c_ch := fun x k => chi1.c_ch x k * chi2.c_ch x k }

/-- [II.P14] Character multiplication preserves idempotent support:
    if chi1 and chi2 are idempotent-supported, then chi1 * chi2 is also
    idempotent-supported.

    Proof: multiplication in sector coordinates is componentwise:
    (B1, C1) * (B2, C2) = (B1*B2, C1*C2).
    e_plus * (B1*B2, C1*C2) = (B1*B2, 0) and
    e_minus * (B1*B2, C1*C2) = (0, C1*C2). -/
def character_mul_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- Product of canonical and chi_plus characters
      let prod_char := IdempotentCharacter.mul canonical_character chi_plus_character
      let prod_val := prod_char.eval x k
      -- Check idempotent support of the product
      let proj_plus := SectorPair.mul e_plus_sector prod_val
      let proj_minus := SectorPair.mul e_minus_sector prod_val
      let recovery := SectorPair.add proj_plus proj_minus == prod_val
      let b_ok := proj_plus.c_sector == 0
      let c_ok := proj_minus.b_sector == 0
      recovery && b_ok && c_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- RING STRUCTURE VERIFICATION [II.P14]
-- ============================================================

/-- Zero character: the additive identity. -/
def zero_character : IdempotentCharacter :=
  { b_ch := fun _ _ => 0, c_ch := fun _ _ => 0 }

/-- Unit character: the multiplicative identity. -/
def unit_character : IdempotentCharacter :=
  { b_ch := fun _ _ => 1, c_ch := fun _ _ => 1 }

/-- [II.P14] Ring axiom: additive identity check.
    chi + 0 = chi for the canonical character. -/
def character_add_identity_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let orig := canonical_character.eval x k
      let sum := (IdempotentCharacter.add canonical_character zero_character).eval x k
      (orig == sum) && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.P14] Ring axiom: multiplicative identity check.
    chi * 1 = chi for the canonical character. -/
def character_mul_identity_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let orig := canonical_character.eval x k
      let prod := (IdempotentCharacter.mul canonical_character unit_character).eval x k
      (orig == prod) && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.P14] Ring axiom: distributivity check.
    chi1 * (chi2 + chi3) = chi1*chi2 + chi1*chi3. -/
def character_distributive_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let chi1 := canonical_character
      let chi2 := chi_plus_character
      let chi3 := chi_minus_character
      -- chi1 * (chi2 + chi3)
      let lhs := (IdempotentCharacter.mul chi1 (IdempotentCharacter.add chi2 chi3)).eval x k
      -- chi1*chi2 + chi1*chi3
      let rhs := (IdempotentCharacter.add
                    (IdempotentCharacter.mul chi1 chi2)
                    (IdempotentCharacter.mul chi1 chi3)).eval x k
      (lhs == rhs) && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL BOUNDARY CHARACTERS CHECK [II.D59 + II.P14]
-- ============================================================

/-- [II.D59 + II.P14] Complete boundary character verification:
    - Idempotent decomposition (II.D59)
    - Tower coherence (II.D59)
    - Addition preserves support (II.P14)
    - Multiplication preserves support (II.P14)
    - Ring axioms: additive identity, multiplicative identity, distributivity -/
def full_boundary_characters_check (bound db : TauIdx) : Bool :=
  idemp_character_check bound db &&
  character_tower_check bound db &&
  character_add_check bound db &&
  character_mul_check bound db &&
  character_add_identity_check bound db &&
  character_mul_identity_check bound db &&
  character_distributive_check bound db

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [II.D59] Idempotent decomposition is always valid:
    e_plus * sp + e_minus * sp = sp for any SectorPair sp.
    This is the algebraic core of idempotent support. -/
theorem idemp_decomp_recovery (sp : SectorPair) :
    SectorPair.add (SectorPair.mul e_plus_sector sp)
                   (SectorPair.mul e_minus_sector sp) = sp := by
  simp [SectorPair.add, SectorPair.mul, e_plus_sector, e_minus_sector]

/-- [II.D59] The B-channel projection kills the C-sector. -/
theorem b_channel_kills_c (sp : SectorPair) :
    (SectorPair.mul e_plus_sector sp).c_sector = 0 := by
  simp [SectorPair.mul, e_plus_sector]

/-- [II.D59] The C-channel projection kills the B-sector. -/
theorem c_channel_kills_b (sp : SectorPair) :
    (SectorPair.mul e_minus_sector sp).b_sector = 0 := by
  simp [SectorPair.mul, e_minus_sector]

/-- [II.D59] Character tower coherence: the canonical character input
    at stage k equals the stage-(k+1) input reduced.
    reduce(reduce(x, k+1), k) = reduce(x, k). -/
theorem character_tower_structural (x : TauIdx) {k : TauIdx} (_ : k ≤ k + 1) :
    reduce (reduce x (k + 1)) k = reduce x k :=
  reduction_compat x (Nat.le_succ k)

/-- [II.P14] Character addition preserves idempotent support (structural):
    for any sp1 sp2, the sum sp1 + sp2 satisfies the decomposition. -/
theorem character_add_structural (sp1 sp2 : SectorPair) :
    SectorPair.add (SectorPair.mul e_plus_sector (SectorPair.add sp1 sp2))
                   (SectorPair.mul e_minus_sector (SectorPair.add sp1 sp2))
    = SectorPair.add sp1 sp2 :=
  idemp_decomp_recovery (SectorPair.add sp1 sp2)

/-- [II.P14] Character multiplication preserves idempotent support (structural):
    for any sp1 sp2, the product sp1 * sp2 satisfies the decomposition. -/
theorem character_mul_structural (sp1 sp2 : SectorPair) :
    SectorPair.add (SectorPair.mul e_plus_sector (SectorPair.mul sp1 sp2))
                   (SectorPair.mul e_minus_sector (SectorPair.mul sp1 sp2))
    = SectorPair.mul sp1 sp2 :=
  idemp_decomp_recovery (SectorPair.mul sp1 sp2)

/-- [II.P14] Distributivity of sector multiplication over addition. -/
theorem sector_distributive (a b c : SectorPair) :
    SectorPair.mul a (SectorPair.add b c) =
    SectorPair.add (SectorPair.mul a b) (SectorPair.mul a c) := by
  simp [SectorPair.mul, SectorPair.add, SectorPair.mk.injEq]
  constructor <;> ring

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Canonical character evaluation
#eval canonical_character.eval 7 2     -- from_tau_idx(7 % 6) = from_tau_idx(1)
#eval canonical_character.eval 12 2    -- from_tau_idx(12 % 6) = from_tau_idx(0)
#eval canonical_character.eval 64 3    -- from_tau_idx(64 % 30) = from_tau_idx(4)

-- Idempotent decomposition check
#eval idemp_character_check 20 4       -- true

-- Character tower coherence
#eval character_tower_check 20 4       -- true

-- Character addition
#eval character_add_check 15 3         -- true

-- Character multiplication
#eval character_mul_check 15 3         -- true

-- Ring axioms
#eval character_add_identity_check 15 3    -- true
#eval character_mul_identity_check 15 3    -- true
#eval character_distributive_check 15 3    -- true

-- Full check
#eval full_boundary_characters_check 15 3  -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Idempotent decomposition [II.D59]
theorem idemp_char_20_4 :
    idemp_character_check 20 4 = true := by native_decide

-- Character tower coherence [II.D59]
theorem char_tower_20_4 :
    character_tower_check 20 4 = true := by native_decide

-- Character addition [II.P14]
theorem char_add_15_3 :
    character_add_check 15 3 = true := by native_decide

-- Character multiplication [II.P14]
theorem char_mul_15_3 :
    character_mul_check 15 3 = true := by native_decide

-- Ring axioms [II.P14]
theorem char_add_id_15_3 :
    character_add_identity_check 15 3 = true := by native_decide

theorem char_mul_id_15_3 :
    character_mul_identity_check 15 3 = true := by native_decide

theorem char_distrib_15_3 :
    character_distributive_check 15 3 = true := by native_decide

-- Full boundary characters [II.D59 + II.P14]
theorem full_bnd_char_15_3 :
    full_boundary_characters_check 15 3 = true := by native_decide

end Tau.BookII.CentralTheorem

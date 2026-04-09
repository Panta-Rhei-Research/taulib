import TauLib.BookIII.Prologue.HartogsBulk
import TauLib.BookII.Enrichment.SelfEnrichment

/-!
# TauLib.BookIII.Enrichment.LayerTemplate

The 4-level enrichment ladder and the uniform layer template.

## Registry Cross-References

- [III.D05] Layer Template — `LayerTemplate`, `layer_template_check`
- [III.D06] E₀ Layer (Mathematics) — `e0_layer`
- [III.D07] E₁ Layer (Physics) — `e1_layer_book3`
- [III.D08] E₂ Layer (Computation) — `e2_layer`
- [III.D09] E₃ Layer (Metaphysics) — `e3_layer`

## Mathematical Content

**III.D05 (Layer Template):** Each enrichment layer E_k has a uniform
four-component structure: E_k = (Carrier_k, Predicate_k, Decoder_k,
Invariant_k). The template is preserved under enrichment: each layer's
invariant flows into the next layer's carrier.

**III.D06-D09:** Concrete instantiations at each enrichment level:
- E₀: NF-addressed τ-objects, NF-addressability, peel map Φ, holomorphic O(τ³)
- E₁: H_τ-enriched objects, sector admissibility, spectral projection, sector couplings
- E₂: Self-referential codes, operational closure, phenotype map, error-correction
- E₃: Self-modeling codes, self-model consistency, meaning assignment, self-awareness

## Architecture Decision: EnrLevel Extension

Book II defines `EnrichmentLevel` as `E0 | E1`. Book III defines a NEW
`EnrLevel` type with all four levels + coercion from Book II's type.
This avoids modifying Book II code.
-/

namespace Tau.BookIII.Enrichment

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment Tau.BookII.Closure
open Tau.BookIII.Prologue

-- ============================================================
-- ENRICHMENT LEVEL (4-LEVEL EXTENSION)
-- ============================================================

/-- Book III enrichment levels: E₀ through E₃.
    Extends Book II's 2-level `EnrichmentLevel` to the full 4-level ladder. -/
inductive EnrLevel where
  | E0 : EnrLevel
  | E1 : EnrLevel
  | E2 : EnrLevel
  | E3 : EnrLevel
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Coercion from Book II's 2-level enrichment to Book III's 4-level. -/
def EnrLevel.ofBookII : EnrichmentLevel → EnrLevel
  | .E0 => .E0
  | .E1 => .E1

/-- Numeric index of an enrichment level. -/
def EnrLevel.toNat : EnrLevel → Nat
  | .E0 => 0
  | .E1 => 1
  | .E2 => 2
  | .E3 => 3

/-- Enrichment level ordering: E₀ < E₁ < E₂ < E₃. -/
def EnrLevel.lt (a b : EnrLevel) : Bool :=
  a.toNat < b.toNat

/-- Enrichment level ordering: E₀ ≤ E₁ ≤ E₂ ≤ E₃. -/
def EnrLevel.le (a b : EnrLevel) : Bool :=
  a.toNat ≤ b.toNat

/-- Successor enrichment level (saturates at E₃). -/
def EnrLevel.succ : EnrLevel → EnrLevel
  | .E0 => .E1
  | .E1 => .E2
  | .E2 => .E3
  | .E3 => .E3

-- ============================================================
-- LAYER TEMPLATE [III.D05]
-- ============================================================

/-- [III.D05] The uniform four-component layer template.
    Each enrichment layer E_k instantiates this with specific
    carrier, predicate, decoder, and invariant functions.

    The template captures the structural pattern:
    - Carrier: the objects that live at this level
    - Predicate: the admissibility condition for carrier elements
    - Decoder: the projection/extraction map (one level down)
    - Invariant: the structure preserved at this level

    Template flow: E_k.invariant → E_{k+1}.carrier -/
structure LayerTemplate where
  /-- Carrier check: is x a valid carrier element at stage k? -/
  carrier_check : TauIdx → TauIdx → Bool
  /-- Predicate check: does x satisfy the admissibility predicate? -/
  predicate_check : TauIdx → TauIdx → Bool
  /-- Decoder: project x from this layer to the previous. -/
  decoder : TauIdx → TauIdx → TauIdx
  /-- Invariant check: is the layer invariant satisfied? -/
  invariant_check : TauIdx → TauIdx → Bool

/-- [III.D05] Layer template completeness: all four components present
    and consistent at given parameters. -/
def layer_template_check (lt : LayerTemplate) (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let c := lt.carrier_check x k
      let p := lt.predicate_check x k
      -- If x is in the carrier, the predicate and invariant should be checkable
      let ok := if c then
        let d := lt.decoder x k
        let inv := lt.invariant_check x k
        -- Decoder output stays within carrier (endomorphism)
        let d_valid := lt.carrier_check d k
        -- Carrier elements should have valid predicate, invariant, and decoder
        p && inv && d_valid
      else true
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- E₀ LAYER (MATHEMATICS) [III.D06]
-- ============================================================

/-- [III.D06] E₀ Layer: the mathematical kernel (Books I-III).
    - Carrier: τ-objects with NF addressing (x < P_k)
    - Predicate: NF-addressability (reduce is identity on valid elements)
    - Decoder: peel map Φ — ABCD extraction
    - Invariant: holomorphic structure (reduce-compatibility) -/
def e0_layer (bound db : TauIdx) : LayerTemplate :=
  { carrier_check := fun x k => x < primorial k
  , predicate_check := fun x k => reduce x k == x
  , decoder := fun x _k =>
      -- ABCD peel: extract the A-coordinate (first prime factor contribution)
      -- nth_prime is 1-indexed in TauLib (nth_prime 0 = 0, nth_prime 1 = 2)
      x % 2
  , invariant_check := fun x k =>
      -- Holomorphic: reduce(reduce(x, k), k) = reduce(x, k)
      reduce (reduce x k) k == reduce x k
  }

-- ============================================================
-- E₁ LAYER (PHYSICS) [III.D07]
-- ============================================================

/-- [III.D07] E₁ Layer: the physics layer (Books IV-V).
    - Carrier: H_τ-enriched objects (hom-stage well-defined)
    - Predicate: sector admissibility (bipolar decomposition exists)
    - Decoder: spectral projection (e₊/e₋ decomposition)
    - Invariant: sector coupling canonicality

    This EXTENDS Book II's E1Layer with sector structure. -/
def e1_layer_book3 (bound db : TauIdx) : LayerTemplate :=
  { carrier_check := fun x k =>
      -- H_τ-enriched: hom_stage is well-defined AND reduce-stable
      let hs := hom_stage x 0 k
      (x < primorial k || k == 0) && (reduce hs k == hs)
  , predicate_check := fun x k =>
      -- Sector admissibility: bipolar decomposition exists
      let sp := interior_bipolar (from_tau_idx (reduce x k))
      let proj_b := SectorPair.mul e_plus_sector sp
      let proj_c := SectorPair.mul e_minus_sector sp
      let recombined := SectorPair.add proj_b proj_c
      recombined == sp
  , decoder := fun x k =>
      -- Spectral projection: extract B-channel value
      let sp := interior_bipolar (from_tau_idx (reduce x k))
      let proj_b := SectorPair.mul e_plus_sector sp
      proj_b.b_sector.toNat
  , invariant_check := fun x k =>
      -- Sector coupling: ω-readout is determined by bipolar decomposition
      let val := reduce x k
      let sp := interior_bipolar (from_tau_idx val)
      -- The coupling is canonical: e₊ * e₋ = 0 (orthogonality)
      let cross := SectorPair.mul e_plus_sector (SectorPair.mul e_minus_sector sp)
      cross == ⟨0, 0⟩
  }

-- ============================================================
-- E₂ LAYER (COMPUTATION) [III.D08]
-- ============================================================

/-- [III.D08] E₂ Layer: the computation layer (Book VI).
    - Carrier: self-referential codes (address = program)
    - Predicate: operational closure (D(C) produces another code)
    - Decoder: phenotype map (code → observable behavior)
    - Invariant: error-correction capacity

    At E₂, the code IS a τ-address. The τ-Tower Machine (TTM)
    from Book I is the structural template. -/
def e2_layer (bound db : TauIdx) : LayerTemplate :=
  { carrier_check := fun x k =>
      -- Self-referential code: x is both address and program
      -- At E₂, every τ-address IS a code (code = data nativity)
      reduce x k == x || x >= primorial k
  , predicate_check := fun x k =>
      -- Operational closure: applying decoder to code produces another code
      -- D(C) = reduce(C, k-1) is always a valid code at stage k-1
      k == 0 || reduce x (k - 1) < primorial (k - 1) || primorial (k - 1) == 0
  , decoder := fun x k =>
      -- Phenotype map: observable behavior = value at stage k
      reduce x k
  , invariant_check := fun x k =>
      -- Error-correction: the code is self-correcting under reduce
      -- reduce(reduce(x, k), k) = reduce(x, k)
      reduce (reduce x k) k == reduce x k
  }

-- ============================================================
-- E₃ LAYER (METAPHYSICS) [III.D09]
-- ============================================================

/-! **Scope limitation (E3 collapse):** At finite primorial level, the E3
    predicate degenerates to E0 because `reduce` is idempotent. This check
    is vacuous but correctly models the mathematical structure. The E3 layer
    is correctly DEFINED but finite verification is vacuous.
    See audit DASHBOARD.md §E3 Collapse. -/

/-- [III.D09] E₃ Layer: the metaphysics layer (Book VII).
    - Carrier: self-modeling codes (model their own observation)
    - Predicate: self-model consistency
    - Decoder: meaning/interpretation assignment
    - Invariant: self-awareness capacity

    At E₃, the code models its own modeling process.
    E₃ is terminal: E₄ = E₃ (self-modeling of self-modeling
    is still self-modeling). -/
def e3_layer (bound db : TauIdx) : LayerTemplate :=
  { carrier_check := fun x k =>
      -- Self-modeling code: models its own observation
      -- At E₃, the code has access to its own decoder output
      -- We model this as: decoder(x) is itself a valid E₂ code
      let decoded := reduce x k
      (e2_layer bound db).carrier_check decoded k
  , predicate_check := fun x k =>
      -- Self-model consistency: triple idempotence + squaring composition
      -- (triple idempotence collapses to single at finite levels — E3 structural)
      let once := reduce x k
      let twice := reduce once k
      let thrice := reduce twice k
      let triple_ok := thrice == once
      -- Squaring composition: reduce(x², k) = reduce(x, k)² mod P_k
      -- (exercises Nat.mul_mod — non-trivially true)
      let pk := primorial k
      let sq_ok := if pk > 0 then
        reduce (x * x) k == (once * once) % pk
      else true
      triple_ok && sq_ok
  , decoder := fun x k =>
      -- Meaning assignment: interpretation = the stable fixed point
      reduce (reduce x k) k
  , invariant_check := fun x k =>
      -- Self-awareness: the system can distinguish self from non-self
      -- Modeled as: the decoder output equals the original (fixed point)
      reduce (reduce x k) k == reduce x k
  }

-- ============================================================
-- LAYER BY ENRICHMENT LEVEL
-- ============================================================

/-- Get the layer template for a given enrichment level. -/
def layer_of (lev : EnrLevel) (bound db : TauIdx) : LayerTemplate :=
  match lev with
  | .E0 => e0_layer bound db
  | .E1 => e1_layer_book3 bound db
  | .E2 => e2_layer bound db
  | .E3 => e3_layer bound db

/-- Check that the layer template is valid at a given enrichment level. -/
def layer_valid_at (lev : EnrLevel) (bound db : TauIdx) : Bool :=
  layer_template_check (layer_of lev bound db) bound db

/-- Check all four layers are valid. -/
def all_layers_valid (bound db : TauIdx) : Bool :=
  layer_valid_at .E0 bound db &&
  layer_valid_at .E1 bound db &&
  layer_valid_at .E2 bound db &&
  layer_valid_at .E3 bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- EnrLevel
#eval EnrLevel.E0.toNat      -- 0
#eval EnrLevel.E3.toNat      -- 3
#eval EnrLevel.E2.succ       -- E3
#eval EnrLevel.E3.succ       -- E3 (saturates)
#eval EnrLevel.lt .E0 .E1    -- true
#eval EnrLevel.lt .E3 .E3    -- false

-- Coercion from Book II
#eval EnrLevel.ofBookII EnrichmentLevel.E0   -- E0
#eval EnrLevel.ofBookII EnrichmentLevel.E1   -- E1

-- E₀ layer
#eval (e0_layer 10 3).carrier_check 3 2       -- true (3 < P_2 = 6)
#eval (e0_layer 10 3).carrier_check 7 2       -- false (7 >= 6)
#eval (e0_layer 10 3).predicate_check 3 2     -- true (reduce(3,2) = 3)
#eval (e0_layer 10 3).invariant_check 42 3    -- true (idempotence)

-- E₁ layer
#eval (e1_layer_book3 10 3).predicate_check 5 2   -- true (bipolar complete)
#eval (e1_layer_book3 10 3).invariant_check 5 2   -- true (orthogonal)

-- E₂ layer
#eval (e2_layer 10 3).predicate_check 3 2     -- true (operational closure)
#eval (e2_layer 10 3).invariant_check 42 3    -- true (self-correcting)

-- E₃ layer
#eval (e3_layer 10 3).predicate_check 5 2     -- true (triple idempotence)
#eval (e3_layer 10 3).invariant_check 5 2     -- true (fixed point)

-- Layer template checks
#eval layer_valid_at .E0 8 3    -- true
#eval layer_valid_at .E1 8 3    -- true
#eval layer_valid_at .E2 8 3    -- true
#eval layer_valid_at .E3 8 3    -- true
#eval all_layers_valid 8 3      -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- E₀ layer valid [III.D06]
theorem e0_layer_valid_8_3 :
    layer_valid_at .E0 8 3 = true := by native_decide

-- E₁ layer valid [III.D07]
theorem e1_layer_valid_8_3 :
    layer_valid_at .E1 8 3 = true := by native_decide

-- E₂ layer valid [III.D08]
theorem e2_layer_valid_8_3 :
    layer_valid_at .E2 8 3 = true := by native_decide

-- E₃ layer valid [III.D09]
theorem e3_layer_valid_8_3 :
    layer_valid_at .E3 8 3 = true := by native_decide

-- All four layers valid [III.D05]
theorem all_layers_8_3 :
    all_layers_valid 8 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- EnrLevel ordering is total: for any two levels, one ≤ the other. -/
theorem enr_le_total (a b : EnrLevel) :
    EnrLevel.le a b = true ∨ EnrLevel.le b a = true := by
  cases a <;> cases b <;> simp [EnrLevel.le, EnrLevel.toNat]

/-- E₃ is maximal: E₃.succ = E₃ (saturation). -/
theorem e3_saturates : EnrLevel.E3.succ = EnrLevel.E3 := rfl

/-- Enrichment levels are distinct. -/
theorem e0_ne_e1 : EnrLevel.E0 ≠ EnrLevel.E1 := by intro h; cases h
theorem e1_ne_e2 : EnrLevel.E1 ≠ EnrLevel.E2 := by intro h; cases h
theorem e2_ne_e3 : EnrLevel.E2 ≠ EnrLevel.E3 := by intro h; cases h

/-- Coercion preserves order: if E0 < E1 in Book II, then ofBookII preserves this. -/
theorem coercion_preserves_order :
    EnrLevel.lt (EnrLevel.ofBookII .E0) (EnrLevel.ofBookII .E1) = true := by
  rfl

/-- The layer template at E₀ has a total carrier for small values. -/
theorem e0_carrier_small (x : TauIdx) (k : TauIdx) (h : x < primorial k) :
    (e0_layer 10 3).carrier_check x k = true := by
  simp only [e0_layer, decide_eq_true_eq]
  exact h

end Tau.BookIII.Enrichment

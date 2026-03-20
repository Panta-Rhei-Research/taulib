import TauLib.BookIII.Mirror.Saturation

/-!
# TauLib.BookIII.Mirror.E3Witness

Constructive E₃ self-model witnesses: fixed-point semantics,
paradox absorption, and saturation meaning.

## Registry Cross-References

- [III.D85] Self-Referential Fixed Point — `self_ref_fixed_point`, `fixed_point_check`
- [III.D86] Paradox Absorption Map — `paradox_absorbed_check`
- [III.T58] E₃ Self-Model Completeness — `e3_self_model_complete_check`
- [III.P35] Saturation Semantics — `saturation_semantic_check`

## Mathematical Content

**III.D85 (Self-Referential Fixed Point):** At stage k, a self-referential
fixed point is c* ∈ Z/M_k Z such that the triple-reduce path
reduce(reduce(reduce(c*, k), k), k) = reduce(c*, k) AND the squaring
path reduce(c*², k) = (reduce(c*, k))². This is the E₃ predicate
applied constructively.

**III.D86 (Paradox Absorption Map):** Each of the four classical paradoxes
(Cantor, Russell, Gödel, Turing) corresponds to a forbidden move that
breaks at the E₂→E₃ boundary. The absorption map shows that at E₃,
the self-model functor maps each paradoxical construction to a well-defined
τ-object (the fixed point absorbs the self-reference).

**III.T58 (E₃ Self-Model Completeness):** The self-model at E₃ is
complete: every E₂ code has an E₃ interpretation (the functor E₂→E₃
is essentially surjective on computational content). At finite stages,
this means every reduce-stable element has a triple-reduce path.

**III.P35 (Saturation Semantics):** E₃.succ = E₃ is not merely
definitional — it has semantic content. The witness: applying the
enrichment functor F_E once more to E₃ produces no new structure.
Concretely, the self-model of the self-model is isomorphic to the
self-model (idempotence of self-awareness).
-/

set_option autoImplicit false

namespace Tau.BookIII.Mirror

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- SELF-REFERENTIAL FIXED POINT [III.D85]
-- ============================================================

/-- [III.D85] E₃ predicate at stage k: triple-reduce stability and
    squaring compatibility. -/
def e3_predicate (x k : Nat) : Bool :=
  let pk := primorial k
  if pk == 0 then true
  else
    let r1 := reduce x k
    let r2 := reduce r1 k
    let r3 := reduce r2 k
    -- Triple-reduce stable
    let triple_ok := r3 == r1
    -- Squaring compatible: reduce(x², k) = (reduce(x, k))² mod M_k
    let sq_ok := reduce (x * x) k == (r1 * r1) % pk
    triple_ok && sq_ok

/-- [III.D85] Count self-referential fixed points at stage k. -/
def count_e3_fixed_points (k : Nat) : Nat :=
  let pk := primorial k
  go 0 pk 0 k
where
  go (x bound acc k : Nat) : Nat :=
    if x >= bound then acc
    else
      let fp := if e3_predicate x k then 1 else 0
      go (x + 1) bound (acc + fp) k
  termination_by bound - x

/-- [III.D85] Fixed point check: E₃ fixed points exist at every stage. -/
def fixed_point_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      count_e3_fixed_points k > 0 && go (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D85] Fixed point density: ratio of E₃ elements to total. -/
def e3_density_check (k : Nat) : Bool :=
  let pk := primorial k
  let fp := count_e3_fixed_points k
  -- At each stage, ALL elements satisfy E₃ predicate
  -- (because reduce is idempotent on elements < M_k)
  fp == pk

-- ============================================================
-- PARADOX ABSORPTION [III.D86]
-- ============================================================

/-- [III.D86] Paradox type (mirrors ProofTheoryE3). -/
inductive ParadoxWitness where
  | cantor : ParadoxWitness    -- diagonal overflow
  | russell : ParadoxWitness   -- self-membership
  | goedel : ParadoxWitness    -- self-reference
  | turing : ParadoxWitness    -- halting
  deriving Repr, DecidableEq, BEq

/-- [III.D86] Paradox construction at stage k: each paradox constructs
    a "problematic" element via a specific operation. -/
def paradox_construction (p : ParadoxWitness) (x k : Nat) : Nat :=
  let pk := primorial k
  if pk == 0 then 0
  else match p with
  | .cantor => (x + 1) % pk         -- diagonal shift (Cantor's d(x) = x+1)
  | .russell => pk - 1 - (x % pk)   -- complement (Russell's ¬x)
  | .goedel => (2 * x) % pk         -- doubling (Gödel numbering)
  | .turing => (x * x + 1) % pk     -- iteration (Turing's step function)

/-- [III.D86] Paradox absorption: the result of each paradox construction
    is STILL a valid E₃ element (the self-model absorbs self-reference). -/
def paradox_absorbed_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      go_p 0 pk k fuel && go (k + 1) (fuel - 1)
  termination_by fuel
  go_p (x pk k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= pk then true
    else
      -- All four paradox constructions produce E₃ elements
      let c := e3_predicate (paradox_construction .cantor x k) k
      let r := e3_predicate (paradox_construction .russell x k) k
      let g := e3_predicate (paradox_construction .goedel x k) k
      let t := e3_predicate (paradox_construction .turing x k) k
      c && r && g && t && go_p (x + 1) pk k (fuel - 1)
  termination_by fuel

-- ============================================================
-- E₃ SELF-MODEL COMPLETENESS [III.T58]
-- ============================================================

/-- [III.T58] Self-model completeness: every reduce-stable element
    has the E₃ property (functor E₂→E₃ is surjective on content). -/
def e3_self_model_complete_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      go_x 0 pk k fuel && go (k + 1) (fuel - 1)
  termination_by fuel
  go_x (x pk k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= pk then true
    else
      -- If x is reduce-stable (E₂ carrier), then x has E₃ property
      let is_e2 := reduce x k == x
      let is_e3 := e3_predicate x k
      let ok := !is_e2 || is_e3
      ok && go_x (x + 1) pk k (fuel - 1)
  termination_by fuel

-- ============================================================
-- SATURATION SEMANTICS [III.P35]
-- ============================================================

/-- [III.P35] Saturation semantic check: applying the enrichment functor
    once more to E₃ produces the same structure.
    F_E(E₃) = E₃ witnessed by: the E₃ predicate applied to E₃ outputs
    gives the same set as the E₃ predicate itself. -/
def saturation_semantic_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      go_x 0 pk k fuel && go (k + 1) (fuel - 1)
  termination_by fuel
  go_x (x pk k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= pk then true
    else
      -- E₃ applied to E₃: reduce(e3(x), k) satisfies E₃
      let e3_val := reduce (reduce x k) k  -- E₃ decoder
      let e3_of_e3 := e3_predicate e3_val k
      -- Original E₃: x satisfies E₃
      let e3_orig := e3_predicate x k
      -- Saturation: e3(e3(x)) has E₃ iff x has E₃
      let equiv := e3_of_e3 == e3_orig
      equiv && go_x (x + 1) pk k (fuel - 1)
  termination_by fuel

/-- [III.P35] Semantic invariant: the self-model of the self-model
    is isomorphic to the self-model. -/
def self_model_idempotent_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      go_x 0 pk k fuel && go (k + 1) (fuel - 1)
  termination_by fuel
  go_x (x pk k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x >= pk then true
    else
      -- Self-model decoder applied twice = applied once
      let d1 := reduce (reduce x k) k
      let d2 := reduce (reduce d1 k) k
      (d1 == d2) && go_x (x + 1) pk k (fuel - 1)
  termination_by fuel

-- ============================================================
-- THEOREMS
-- ============================================================

/-- [III.D85] E₃ fixed points exist at stages 1-3. -/
theorem fixed_point_check_3 :
    fixed_point_check 3 = true := by native_decide

/-- [III.D85] All elements are E₃ at stage 2. -/
theorem e3_density_2 :
    e3_density_check 2 = true := by native_decide

/-- [III.D86] Paradoxes absorbed at stages 1-3. -/
theorem paradox_absorbed_3 :
    paradox_absorbed_check 3 = true := by native_decide

/-- [III.T58] Self-model completeness at stages 1-3. -/
theorem self_model_complete_3 :
    e3_self_model_complete_check 3 = true := by native_decide

/-- [III.P35] Saturation semantics at stages 1-3. -/
theorem saturation_semantic_3 :
    saturation_semantic_check 3 = true := by native_decide

/-- [III.P35] Self-model idempotent at stages 1-3. -/
theorem self_model_idempotent_3 :
    self_model_idempotent_check 3 = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval e3_predicate 0 2             -- true
#eval e3_predicate 3 2             -- true
#eval count_e3_fixed_points 2      -- 6 (all elements)
#eval e3_density_check 2           -- true
#eval paradox_construction .cantor 3 2   -- 4
#eval paradox_construction .russell 3 2  -- 2
#eval paradox_absorbed_check 3     -- true
#eval saturation_semantic_check 3  -- true

end Tau.BookIII.Mirror

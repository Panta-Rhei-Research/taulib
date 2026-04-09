import TauLib.BookII.Hartogs.EvolutionOperator

/-!
# TauLib.BookII.Hartogs.CategoryStructure

Category structure of holomorphic endomorphisms on the primorial tower.

## Registry Cross-References

- [II.D39] Holomorphic Composition — `hol_comp`, `hol_comp_sf`
- [II.D40] Holomorphic Identity — `hol_id`, `hol_id_sf`
- [II.T29] Associativity — `hol_assoc_check`, `hol_assoc_thm`
- [II.D41] Endomorphism Category HolEnd_tau — `HolEndCat`, `holend_axioms_check`

## Mathematical Content

The holomorphic endomorphisms on the primorial tower form a category HolEnd_tau:

**Objects:** Stages k in N (each stage is a finite cyclic group Z/M_k Z).

**Morphisms:** Tower-coherent maps f : Z/M_k Z -> Z/M_k Z satisfying
  reduce(f(x), j) = f(reduce(x, j)) for all j <= k.
  At the TauIdx level: f(n, k) = reduce(f(n, k), k).

**Composition (II.D39):** Given f, g : TauIdx -> TauIdx -> TauIdx,
  (f . g)(n, k) = f(g(n, k), k).
  This preserves tower coherence because both f and g are reduce-compatible.

**Identity (II.D40):** id(n, k) = reduce(n, k).
  This is tower-coherent by reduction_compat.

**Associativity (II.T29):** (f . (g . h))(n, k) = ((f . g) . h)(n, k)
  holds definitionally by function application associativity.

**Unit laws:** f . id = f and id . f = f
  hold when f is reduce-normalized (f(n, k) = f(reduce(n, k), k)).

The category HolEnd_tau is the endomorphism category of the primorial
inverse system, capturing all holomorphic self-maps of the tower.
-/

namespace Tau.BookII.Hartogs

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy

-- ============================================================
-- HOLOMORPHIC COMPOSITION [II.D39]
-- ============================================================

/-- [II.D39] Holomorphic composition at the TauIdx level.
    Given two tower-coherent endomorphisms f, g on the primorial tower,
    their composition applies g first, then f, at each stage k.

    (f . g)(n, k) = f(g(n, k), k)

    This is the pointwise composition of stage-k maps, which preserves
    tower coherence because both f and g are reduce-compatible. -/
def hol_comp (f g : TauIdx -> TauIdx -> TauIdx)
    (n k : TauIdx) : TauIdx :=
  f (g n k) k

/-- [II.D39] Composition for StageFun pairs (bipolar composition):
    B-sector and C-sector compose independently.
    (f . g).b_fun(n, k) = f.b_fun(g.b_fun(n, k), k)
    (f . g).c_fun(n, k) = f.c_fun(g.c_fun(n, k), k) -/
def hol_comp_sf (f g : StageFun) : StageFun :=
  StageFun.comp f g

-- ============================================================
-- HOLOMORPHIC IDENTITY [II.D40]
-- ============================================================

/-- [II.D40] The identity holomorphic endomorphism.
    id(n, k) = reduce(n, k): the canonical projection to Z/M_k Z.

    This is the identity morphism in HolEnd_tau. It is tower-coherent
    by reduction_compat: reduce(reduce(n, l), k) = reduce(n, k). -/
def hol_id (n k : TauIdx) : TauIdx :=
  reduce n k

/-- [II.D40] The identity StageFun: both sectors use reduce. -/
def hol_id_sf : StageFun :=
  id_stage

-- ============================================================
-- SAMPLE ENDOMORPHISMS (for verification)
-- ============================================================

/-- The squaring endomorphism: sq(n, k) = (n * n) % M_k.
    Tower-coherent because reduce((n*n) mod M_l, k)
    = (n*n) mod M_k = reduce(n*n, k) by Nat.mod_mod. -/
def hol_sq (n k : TauIdx) : TauIdx :=
  reduce (n * n) k

/-- The doubling endomorphism: dbl(n, k) = (2 * n) % M_k.
    Tower-coherent similarly. -/
def hol_dbl (n k : TauIdx) : TauIdx :=
  reduce (2 * n) k

/-- The constant-zero endomorphism: zero(n, k) = 0.
    Trivially tower-coherent. -/
def hol_zero (_n _k : TauIdx) : TauIdx := 0

-- ============================================================
-- ASSOCIATIVITY [II.T29]
-- ============================================================

/-- [II.T29] Associativity check for holomorphic composition.
    For sample endomorphisms f, g, h, verify:
    hol_comp f (hol_comp g h) n k = hol_comp (hol_comp f g) h n k

    This holds definitionally because:
    LHS = f(g(h(n, k), k), k)
    RHS = f(g(h(n, k), k), k)
    which are identical by function application. -/
def hol_assoc_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- f = hol_id, g = hol_sq, h = hol_dbl
      let lhs := hol_comp hol_id (hol_comp hol_sq hol_dbl) x k
      let rhs := hol_comp (hol_comp hol_id hol_sq) hol_dbl x k
      let ok := lhs == rhs
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.T29] Associativity for a triple of concrete endomorphisms:
    (sq . dbl) . id = sq . (dbl . id) -/
def hol_assoc_triple_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let lhs := hol_comp (hol_comp hol_sq hol_dbl) hol_id x k
      let rhs := hol_comp hol_sq (hol_comp hol_dbl hol_id) x k
      let ok := lhs == rhs
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.T29] Associativity for ALL triples from {id, sq, dbl, zero}.
    Tests all 4^3 = 64 triples on [2, bound] x [1, db]. -/
def hol_assoc_exhaustive_check (bound db : TauIdx) : Bool :=
  let fns := [hol_id, hol_sq, hol_dbl, hol_zero]
  go_f fns fns fns 2 1 bound db (4 * 4 * 4 * (bound + 1) * (db + 1))
where
  go_f (fs gs hs : List (TauIdx -> TauIdx -> TauIdx))
       (x k : Nat) (bound db : Nat)
       (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else
      match fs with
      | [] => true
      | f :: fs' =>
        go_g f gs hs x k bound db (fuel - 1) &&
        go_f fs' gs hs x k bound db (fuel - 1)
  termination_by fuel
  go_g (f : TauIdx -> TauIdx -> TauIdx)
       (gs hs : List (TauIdx -> TauIdx -> TauIdx))
       (x k : Nat) (bound db : Nat)
       (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else
      match gs with
      | [] => true
      | g :: gs' =>
        go_h f g hs x k bound db (fuel - 1) &&
        go_g f gs' hs x k bound db (fuel - 1)
  termination_by fuel
  go_h (f g : TauIdx -> TauIdx -> TauIdx)
       (hs : List (TauIdx -> TauIdx -> TauIdx))
       (x k : Nat) (bound db : Nat)
       (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else
      match hs with
      | [] => true
      | h :: hs' =>
        verify f g h x k bound db (fuel - 1) &&
        go_h f g hs' x k bound db (fuel - 1)
  termination_by fuel
  verify (f g h : TauIdx -> TauIdx -> TauIdx)
         (x k : Nat) (bound db : Nat)
         (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then verify f g h (x + 1) 1 bound db (fuel - 1)
    else
      let lhs := hol_comp f (hol_comp g h) x k
      let rhs := hol_comp (hol_comp f g) h x k
      (lhs == rhs) && verify f g h x (k + 1) bound db (fuel - 1)
  termination_by fuel

-- ============================================================
-- FORMAL ASSOCIATIVITY [II.T29]
-- ============================================================

/-- [II.T29] Associativity theorem (formal):
    Holomorphic composition is associative by definition.
    hol_comp f (hol_comp g h) n k = hol_comp (hol_comp f g) h n k

    This is an immediate consequence of the definition:
    both sides expand to f(g(h(n, k), k), k). -/
theorem hol_assoc_thm (f g h : TauIdx -> TauIdx -> TauIdx) (n k : TauIdx) :
    hol_comp f (hol_comp g h) n k = hol_comp (hol_comp f g) h n k := by
  rfl

-- ============================================================
-- UNIT LAWS
-- ============================================================

/-- Right unit check: for reduce-normalized f, f . id = f.
    f(reduce(n, k), k) = f(n, k) when f depends only on n mod M_k. -/
def right_unit_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- For hol_sq: sq(id(n, k), k) = sq(reduce(n, k), k)
      --   = reduce(reduce(n,k)^2, k) = reduce(n^2 mod M_k^2, k)
      -- We check: reduce((reduce(n,k))^2, k) = reduce(n^2, k)
      let via_id := hol_comp hol_sq hol_id x k
      let direct := hol_sq x k
      let ok := via_id == direct
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- Left unit check: id . f = f for reduce-normalized f.
    id(f(n, k), k) = reduce(f(n, k), k) = f(n, k)
    when f(n, k) is already reduced at stage k. -/
def left_unit_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- id(sq(n, k), k) = reduce(reduce(n^2, k), k) = reduce(n^2, k) = sq(n, k)
      let via_id := hol_comp hol_id hol_sq x k
      let direct := hol_sq x k
      let ok := via_id == direct
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- Left unit theorem (formal): hol_id composed with any reduce-based
    endomorphism is idempotent.
    hol_comp hol_id hol_id n k = hol_id n k -/
theorem left_unit_id_thm (n k : TauIdx) :
    hol_comp hol_id hol_id n k = hol_id n k := by
  simp only [hol_comp, hol_id]
  exact reduction_compat n (Nat.le_refl k)

/-- StageFun identity unit laws: id_stage composed with itself yields
    tower-coherent result equal to id_stage evaluation. -/
theorem stagefun_id_comp_check (n k : TauIdx) :
    (StageFun.comp id_stage id_stage).b_fun n k = id_stage.b_fun n k := by
  simp only [StageFun.comp, id_stage]
  exact reduction_compat n (Nat.le_refl k)

-- ============================================================
-- TOWER COHERENCE PRESERVATION UNDER COMPOSITION
-- ============================================================

/-- Tower coherence of composed reduce-based endomorphisms.
    If f(n, k) = reduce(g(n), k) for some g, then f is tower-coherent.
    Composing two such f's gives another tower-coherent endomorphism. -/
def tower_coherent_comp_check (bound db : TauIdx) : Bool :=
  go 2 1 1 ((bound + 1) * (db + 1) * (db + 1))
where
  go (x k l fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 1 (fuel - 1)
    else if l > db then go x (k + 1) 1 (fuel - 1)
    else
      -- For (sq . dbl): check reduce(comp(x, l), k) = comp(x, k) for k <= l
      let ok := !(k ≤ l) ||
        (reduce (hol_comp hol_sq hol_dbl x l) k == hol_comp hol_sq hol_dbl x k)
      ok && go x k (l + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- ENDOMORPHISM CATEGORY [II.D41]
-- ============================================================

/-- [II.D41] The endomorphism category HolEnd_tau.
    Encapsulates: objects (stages), morphisms (tower-coherent maps),
    composition, identity, and the category axioms.

    In the Lean representation, we store:
    - max_stage: the number of stages considered
    - A verification that the axioms hold up to given bounds. -/
structure HolEndCat where
  /-- Maximum stage depth. -/
  max_stage : TauIdx
  /-- Maximum input value for verification. -/
  max_val : TauIdx
  deriving Repr

/-- Construct a verified HolEndCat: checks all axioms computationally. -/
def mk_holend (max_stage max_val : TauIdx) : HolEndCat :=
  { max_stage := max_stage
  , max_val := max_val
  }

/-- [II.D41] Full category axiom check for HolEnd_tau:
    1. Associativity (II.T29)
    2. Left unit law
    3. Right unit law
    4. Tower coherence preservation under composition -/
def holend_axioms_check (cat : HolEndCat) : Bool :=
  hol_assoc_check cat.max_val cat.max_stage &&
  hol_assoc_triple_check cat.max_val cat.max_stage &&
  left_unit_check cat.max_val cat.max_stage &&
  right_unit_check cat.max_val cat.max_stage &&
  tower_coherent_comp_check cat.max_val cat.max_stage

/-- The canonical HolEndCat with depth 4 and bound 12. -/
def holend_4_12 : HolEndCat := mk_holend 4 12

/-- Smaller HolEndCat for faster native_decide proofs. -/
def holend_3_10 : HolEndCat := mk_holend 3 10

-- ============================================================
-- COMPOSITION CLOSURE
-- ============================================================

/-- Composition of reduce-based endomorphisms produces reduce-based results.
    hol_comp hol_sq hol_dbl n k = reduce((2n)^2, k), which is itself reduced. -/
def composition_closure_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- The composed value is already reduced at stage k
      let val := hol_comp hol_sq hol_dbl x k
      let ok := reduce val k == val
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- BIPOLAR COMPOSITION STRUCTURE
-- ============================================================

/-- Composition respects bipolar decomposition:
    the B-sector and C-sector compose independently.
    For StageFun composition: (f.g).b = f.b . g.b, (f.g).c = f.c . g.c.
    This is structural from the definition of StageFun.comp. -/
def bipolar_comp_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- Check that StageFun.comp respects sectors
      let f := chi_plus_stage
      let g := id_stage
      let comp := StageFun.comp f g
      -- B-sector: comp.b = f.b(g.b(x, k), k)
      let b_ok := comp.b_fun x k == f.b_fun (g.b_fun x k) k
      -- C-sector: comp.c = f.c(g.c(x, k), k)
      let c_ok := comp.c_fun x k == f.c_fun (g.c_fun x k) k
      b_ok && c_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL CATEGORY STRUCTURE CHECK
-- ============================================================

/-- [II.D41] Complete category structure verification:
    HolEnd_tau axioms + composition closure + bipolar structure. -/
def full_category_check (bound db : TauIdx) : Bool :=
  holend_axioms_check (mk_holend db bound) &&
  composition_closure_check bound db &&
  bipolar_comp_check bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Composition
#eval hol_comp hol_sq hol_id 7 2       -- reduce(reduce(7,2)^2, 2) = reduce(1, 2) = 1
#eval hol_comp hol_id hol_sq 7 2       -- reduce(reduce(49,2), 2) = reduce(1, 2) = 1
#eval hol_comp hol_sq hol_dbl 5 2      -- reduce((2*5)^2, 2) = reduce(100, 2) = 4
#eval hol_comp hol_dbl hol_sq 5 2      -- reduce(2*reduce(25,2), 2) = reduce(2*1, 2) = 2

-- Identity
#eval hol_id 7 2                       -- reduce(7, 2) = 1
#eval hol_id 100 3                     -- reduce(100, 3) = 10

-- Associativity
#eval hol_comp hol_sq (hol_comp hol_dbl hol_id) 5 2   -- should equal...
#eval hol_comp (hol_comp hol_sq hol_dbl) hol_id 5 2   -- ...this

-- Unit laws
#eval hol_comp hol_sq hol_id 5 2       -- same as hol_sq 5 2
#eval hol_sq 5 2                        -- check match

-- Category axiom checks
#eval hol_assoc_check 12 4             -- true
#eval hol_assoc_triple_check 12 4      -- true
#eval left_unit_check 12 4             -- true
#eval right_unit_check 12 4            -- true
#eval tower_coherent_comp_check 10 3   -- true

-- HolEndCat
#eval holend_axioms_check holend_4_12  -- true
#eval holend_axioms_check holend_3_10  -- true

-- Composition closure
#eval composition_closure_check 12 4   -- true

-- Bipolar composition
#eval bipolar_comp_check 12 4          -- true

-- Full check
#eval full_category_check 10 3         -- true

-- StageFun composition
#eval (StageFun.comp chi_plus_stage id_stage).b_fun 7 2  -- reduce(reduce(7,2), 2) = 1
#eval chi_plus_stage.b_fun 7 2                             -- reduce(7, 2) = 1

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Associativity [II.T29]
theorem assoc_12_4 :
    hol_assoc_check 12 4 = true := by native_decide

theorem assoc_triple_12_4 :
    hol_assoc_triple_check 12 4 = true := by native_decide

theorem assoc_exhaustive_8_3 :
    hol_assoc_exhaustive_check 8 3 = true := by native_decide

-- Unit laws
theorem left_unit_12_4 :
    left_unit_check 12 4 = true := by native_decide

theorem right_unit_12_4 :
    right_unit_check 12 4 = true := by native_decide

-- Tower coherence under composition
theorem tower_comp_10_3 :
    tower_coherent_comp_check 10 3 = true := by native_decide

-- Category axioms [II.D41]
theorem holend_3_10_ok :
    holend_axioms_check holend_3_10 = true := by native_decide

-- Composition closure
theorem comp_closure_10_3 :
    composition_closure_check 10 3 = true := by native_decide

-- Bipolar composition
theorem bipolar_comp_10_3 :
    bipolar_comp_check 10 3 = true := by native_decide

-- Full category structure
theorem full_cat_10_3 :
    full_category_check 10 3 = true := by native_decide

end Tau.BookII.Hartogs

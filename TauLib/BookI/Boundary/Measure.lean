import TauLib.BookI.Boundary.Ring
import TauLib.BookI.Polarity.Polarity
import TauLib.BookI.Polarity.ModArith

/-!
# TauLib.BookI.Boundary.Measure

Constructive measure theory on the primorial tower.

## Registry Cross-References

- [I.D95] τ-Measure Space — `TauMeasureSpace`, `tau_measure_check`
- [I.D96] Tower σ-Algebra — `TowerSigmaAlgebra`, `sigma_algebra_check`
- [I.T49] Countable Additivity — `countable_additivity_check`
- [I.P43] Measure Compatibility — `measure_compatibility_check`

## Mathematical Content

**I.D95 (τ-Measure Space):** At each primorial stage k, the set Z/M_k Z
carries the normalized counting measure μ_k(S) = |S| / M_k. This is the
unique translation-invariant probability measure on the finite cyclic group.
The τ-measure space is the projective family (Z/M_k Z, μ_k)_{k≥1}.

**I.D96 (Tower σ-Algebra):** At finite stage k, every subset of Z/M_k Z is
measurable (the σ-algebra is the full power set). A "tower-measurable" set is
a compatible family of subsets S_k ⊆ Z/M_k Z such that the preimage of S_k
under reduction is S_{k+1} ∩ Z/M_{k+1} Z.

**I.T49 (Countable Additivity):** The stage-k measure is finitely additive
(trivially, since Z/M_k Z is finite). Tower compatibility ensures that
measures at different stages agree: μ_{k+1}(π^{-1}(S_k)) = μ_k(S_k),
where π is the reduction map.

**I.P43 (Measure Compatibility):** The projective family of measures is
compatible: for any tower-measurable set, the measure is independent of
the stage at which it is evaluated.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- PRIMORIAL COUNTING MEASURE [I.D95]
-- ============================================================

/-- [I.D95] Count elements of a predicate-defined subset of Z/M_k Z.
    count_satisfying p k = |{x ∈ [0, M_k) : p(x) = true}|. -/
def count_satisfying (p : Nat → Bool) (k : Nat) : Nat :=
  go 0 (primorial k) 0
where
  go (x bound acc : Nat) : Nat :=
    if x >= bound then acc
    else go (x + 1) bound (if p x then acc + 1 else acc)
  termination_by bound - x

/-- [I.D95] The normalized counting measure: μ_k(S) as a rational
    pair (numerator, denominator) = (|S|, M_k). -/
structure StageMeasure where
  numerator : Nat
  denominator : Nat
  deriving Repr

/-- [I.D95] Compute the stage-k measure of a predicate-defined subset. -/
def stage_measure (p : Nat → Bool) (k : Nat) : StageMeasure :=
  let pk := primorial k
  let count := count_satisfying p k
  { numerator := count
  , denominator := pk }

-- ============================================================
-- TOWER σ-ALGEBRA [I.D96]
-- ============================================================

/-- [I.D96] A tower-measurable set is a family of predicates, one per stage,
    that are compatible under the reduction map. -/
structure TowerMeasurableSet where
  predicate : Nat → Nat → Bool  -- predicate(k, x) = whether x ∈ S_k

/-- [I.D96] Check tower compatibility at stages k and k+1:
    x satisfies S_{k+1} implies reduce(x, k) satisfies S_k. -/
def tower_compatible_check (tms : TowerMeasurableSet) (k : Nat) : Bool :=
  go 0 (primorial (k + 1))
where
  go (x bound : Nat) : Bool :=
    if x >= bound then true
    else
      let ok := if tms.predicate (k + 1) x then
        tms.predicate k (x % primorial k)
      else true
      ok && go (x + 1) bound
  termination_by bound - x

/-- [I.D96] Check tower compatibility for all stages 1..db. -/
def sigma_algebra_check (tms : TowerMeasurableSet) (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k >= db then true
    else tower_compatible_check tms k && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- COUNTABLE ADDITIVITY [I.T49]
-- ============================================================

/-- [I.T49] Disjoint union measure check: for predicates p, q with
    p ∩ q = ∅ at stage k, verify μ(p ∪ q) = μ(p) + μ(q). -/
def disjoint_check (p q : Nat → Bool) (k : Nat) : Bool :=
  go 0 (primorial k)
where
  go (x bound : Nat) : Bool :=
    if x >= bound then true
    else
      let ok := !(p x && q x)  -- disjoint: never both true
      ok && go (x + 1) bound
  termination_by bound - x

/-- [I.T49] Additivity check: if p ∩ q = ∅, then |p ∪ q| = |p| + |q|. -/
def countable_additivity_check (p q : Nat → Bool) (k : Nat) : Bool :=
  if disjoint_check p q k then
    let cp := count_satisfying p k
    let cq := count_satisfying q k
    let cpq := count_satisfying (fun x => p x || q x) k
    cpq == cp + cq
  else true  -- precondition not met, vacuously true

-- ============================================================
-- MEASURE COMPATIBILITY [I.P43]
-- ============================================================

/-- [I.P43] Measure compatibility check: the measure of a tower-measurable
    set at stage k+1 (projected down) equals the measure at stage k.
    Formally: count_{k+1}(S_{k+1}) / M_{k+1} = count_k(S_k) / M_k
    i.e., count_{k+1}(S_{k+1}) * M_k = count_k(S_k) * M_{k+1}. -/
def measure_compatibility_check (tms : TowerMeasurableSet) (k : Nat) : Bool :=
  let pk := primorial k
  let pk1 := primorial (k + 1)
  let ck := count_satisfying (tms.predicate k) k
  let ck1 := count_satisfying (tms.predicate (k + 1)) (k + 1)
  ck1 * pk == ck * pk1

/-- [I.P43] Full measure compatibility for stages 1..db. -/
def measure_compatibility_full (tms : TowerMeasurableSet) (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k >= db then true
    else measure_compatibility_check tms k && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- CANONICAL EXAMPLES
-- ============================================================

/-- The full set: every element satisfies the predicate. -/
def full_set : TowerMeasurableSet :=
  { predicate := fun _ _ => true }

/-- The empty set: no element satisfies the predicate. -/
def empty_set : TowerMeasurableSet :=
  { predicate := fun _ _ => false }

/-- Even elements at each stage. -/
def even_set : TowerMeasurableSet :=
  { predicate := fun _ x => x % 2 == 0 }

/-- B-sector elements (≡ 1 mod 4) at each stage. -/
def b_sector_set : TowerMeasurableSet :=
  { predicate := fun _ x => x % 4 == 1 }

-- ============================================================
-- THEOREMS [I.T49, I.P43]
-- ============================================================

/-- [I.D95] Primorial is always positive (stages 1-3). -/
theorem primorial_pos_1 : primorial 1 > 0 := by native_decide
theorem primorial_pos_2 : primorial 2 > 0 := by native_decide
theorem primorial_pos_3 : primorial 3 > 0 := by native_decide

/-- [I.T49] Additivity for even/odd partition at stage 3. -/
theorem additivity_even_odd_3 :
    countable_additivity_check (fun x => x % 2 == 0)
      (fun x => x % 2 == 1) 3 = true := by native_decide

/-- [I.T49] Additivity for B/C sector partition at stage 3. -/
theorem additivity_bc_3 :
    countable_additivity_check (fun x => x % 4 == 1)
      (fun x => x % 4 == 3) 3 = true := by native_decide

/-- [I.P43] Full set is tower-compatible up to stage 3. -/
theorem full_set_compatible_3 :
    sigma_algebra_check full_set 3 = true := by native_decide

/-- [I.P43] Empty set is tower-compatible up to stage 3. -/
theorem empty_set_compatible_3 :
    sigma_algebra_check empty_set 3 = true := by native_decide

/-- [I.P43] Even set is tower-compatible up to stage 3. -/
theorem even_set_compatible_3 :
    sigma_algebra_check even_set 3 = true := by native_decide

/-- [I.D95] Full set measure at stage 3: M_3 / M_3 = 1. -/
theorem full_set_measure_3 :
    count_satisfying (fun _ => true) 3 = primorial 3 := by native_decide

/-- [I.D95] Empty set measure at stage 3: 0 / M_3 = 0. -/
theorem empty_set_measure_3 :
    count_satisfying (fun _ => false) 3 = 0 := by native_decide

-- ============================================================
-- MEASURE SPACE STRUCTURE [I.D95]
-- ============================================================

/-- [I.D95] The τ-measure space: a collection of stages with
    compatible counting measures. -/
structure TauMeasureSpace where
  max_stage : Nat
  measurable_sets : List TowerMeasurableSet

/-- [I.D95] Validate a τ-measure space: all sets tower-compatible. -/
def tau_measure_check (tms : TauMeasureSpace) : Bool :=
  tms.measurable_sets.all (fun s => sigma_algebra_check s tms.max_stage)

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Primorial values
#eval primorial 1   -- 2
#eval primorial 2   -- 6
#eval primorial 3   -- 30

-- Count even elements mod 30
#eval count_satisfying (fun x => x % 2 == 0) 3  -- 15

-- Count B-sector elements mod 30
#eval count_satisfying (fun x => x % 4 == 1) 3  -- 8

-- Tower compatibility
#eval sigma_algebra_check full_set 3    -- true
#eval sigma_algebra_check empty_set 3   -- true
#eval sigma_algebra_check even_set 3    -- true

-- Additivity
#eval countable_additivity_check (fun x => x % 2 == 0)
  (fun x => x % 2 == 1) 3  -- true

-- Measure compatibility for even set
#eval measure_compatibility_full even_set 3  -- true

end Tau.Boundary

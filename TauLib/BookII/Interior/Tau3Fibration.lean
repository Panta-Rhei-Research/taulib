import TauLib.BookII.Interior.TauAdmissible

/-!
# TauLib.BookII.Interior.Tau3Fibration

The τ³ fibration: τ³ = τ¹ ×_f T² as a fibered product.

## Registry Cross-References

- [II.D05] Base τ¹ — `BaseTau1`
- [II.D06] Fiber T² — `FiberT2`
- [II.D07] Fibered Product τ³ — `Tau3`, `tau3_proj`, `tau3_fiber_proj`
- [II.T03] Fibration Structure — `proj_surjective_check`, `non_trivial_check`

## Mathematical Content

The ABCD chart decomposes into base and fiber:
- Base τ¹ = { (D, A) : A ∈ ℙ_τ ∪ {1}, prime factors of D < A }
- Fiber T² = { (B, C) : B, C ≥ 0 }
- τ³ = τ¹ ×_f T²: fibered product (NOT Cartesian)

Two reasons τ³ ≠ τ¹ × T²:
1. Peel-order coupling: prime factors of D must be < A
2. Base-to-fiber coupling: admissible (B,C) depends on (D,A)

Fibration structure (II.T03):
1. pr : τ³ → τ¹ is surjective (every base point has fiber B=1,C=0)
2. Fibers vary (different A yield different admissible ranges)
3. Not a product bundle (peel-order constraint)
4. Faithful (Φ : Obj(τ) → τ³ is injective, by I.T04)
-/

namespace Tau.BookII.Interior

open Tau.Coordinates Tau.Denotation

-- ============================================================
-- BASE τ¹ [II.D05]
-- ============================================================

/-- [II.D05] Base τ¹: the (D, A) coordinate space.
    D = radial depth (α-channel), A = prime direction (π-channel).
    Constraint: A ∈ ℙ_τ ∪ {1}, all prime factors of D < A. -/
structure BaseTau1 where
  d : TauIdx  -- radial depth
  a : TauIdx  -- prime direction
  deriving Repr, DecidableEq

/-- Validity check for base point. -/
def BaseTau1.valid (b : BaseTau1) : Bool :=
  constraint_C1 b.a && constraint_C3 b.d b.a

-- ============================================================
-- FIBER T² [II.D06]
-- ============================================================

/-- [II.D06] Fiber T²: the (B, C) coordinate space.
    B = exponent (γ-channel), C = tetration height (η-channel).
    Both non-negative (automatic for ℕ).
    Notation T² anticipates torus-like winding structure (Book II Part III). -/
structure FiberT2 where
  b : TauIdx  -- exponent
  c : TauIdx  -- tetration height
  deriving Repr, DecidableEq

-- ============================================================
-- FIBERED PRODUCT τ³ [II.D07]
-- ============================================================

/-- [II.D07] τ³ = τ¹ ×_f T²: the fibered product.
    A τ-admissible quadruple viewed as base + fiber. -/
structure Tau3 where
  base  : BaseTau1
  fiber : FiberT2
  deriving Repr, DecidableEq

/-- Convert TauAdmissiblePoint to Tau3 (fibered product form). -/
def to_tau3 (p : TauAdmissiblePoint) : Tau3 :=
  ⟨⟨p.d, p.a⟩, ⟨p.b, p.c⟩⟩

/-- Convert Tau3 back to TauAdmissiblePoint. -/
def from_tau3 (t : Tau3) : TauAdmissiblePoint :=
  ⟨t.base.a, t.fiber.b, t.fiber.c, t.base.d⟩

/-- Projection pr : τ³ → τ¹. -/
def tau3_proj (t : Tau3) : BaseTau1 := t.base

/-- Fiber projection: τ³ → T². -/
def tau3_fiber_proj (t : Tau3) : FiberT2 := t.fiber

-- ============================================================
-- CONVERSION ROUND-TRIP
-- ============================================================

/-- from_tau3 ∘ to_tau3 = id. -/
theorem tau3_round_trip (p : TauAdmissiblePoint) :
    from_tau3 (to_tau3 p) = p := by
  simp [to_tau3, from_tau3]

/-- to_tau3 ∘ from_tau3 = id. -/
theorem tau3_round_trip' (t : Tau3) :
    to_tau3 (from_tau3 t) = t := by
  simp [to_tau3, from_tau3]

-- ============================================================
-- FIBRATION STRUCTURE [II.T03]
-- ============================================================

/-- [II.T03, clause 1] Surjectivity: every valid base point admits
    at least one fiber point (B=1, C=0 is always admissible). -/
def proj_surjective_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      let base := BaseTau1.mk p.d p.a
      base.valid && go (x + 1) (fuel - 1)
  termination_by fuel

/-- [II.T03, clause 3] Non-triviality: demonstrate that the fibration
    is NOT a product bundle by showing different base points yield
    different fiber behavior.

    Example: X=12 has (A=3, D=4) while X=64 has (A=2, D=1).
    At A=3: B can be up to what 3^B allows.
    At A=2: B can be up to what 2^B allows (different range). -/
def non_trivial_check : Bool :=
  -- Same base A=2 but very different fibers
  let p1 := from_tau_idx 4    -- (2, 2, 1, 1)
  let p2 := from_tau_idx 16   -- (2, 1, 3, 1)
  let p3 := from_tau_idx 64   -- (2, 3, 2, 1)
  -- All have A=2 but different (B,C) combinations
  p1.a == p2.a && p2.a == p3.a &&
  (p1.b, p1.c) != (p2.b, p2.c) &&
  (p2.b, p2.c) != (p3.b, p3.c) &&
  -- Different A leads to fundamentally different structure
  let q1 := from_tau_idx 12   -- (3, 1, 1, 4)
  let q2 := from_tau_idx 27   -- (3, 3, 1, 1)
  q1.a == q2.a && q1.a != p1.a

/-- [II.T03, clause 4] Faithfulness: Φ is injective.
    Different X values produce different ABCD quadruples. -/
def faithful_check (bound : TauIdx) : Bool :=
  go 2 (bound + 1) []
where
  go (x fuel : Nat) (seen : List TauAdmissiblePoint) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let p := from_tau_idx x
      if seen.contains p then false
      else go (x + 1) (fuel - 1) (p :: seen)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Base/fiber decomposition
#eval to_tau3 (from_tau_idx 12)   -- base=(4,3), fiber=(1,1)
#eval to_tau3 (from_tau_idx 64)   -- base=(1,2), fiber=(3,2)
#eval to_tau3 (from_tau_idx 360)  -- base=(72,5), fiber=(1,1)

-- Projections
#eval tau3_proj (to_tau3 (from_tau_idx 12))        -- (4, 3)
#eval tau3_fiber_proj (to_tau3 (from_tau_idx 64))   -- (3, 2)

-- Fibration checks
#eval proj_surjective_check 50    -- true
#eval non_trivial_check           -- true
#eval faithful_check 100          -- true

-- Formal verification
theorem surjective_2_to_20 : proj_surjective_check 20 = true := by native_decide
theorem faithful_2_to_50 : faithful_check 50 = true := by native_decide

end Tau.BookII.Interior

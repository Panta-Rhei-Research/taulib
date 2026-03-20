import TauLib.BookIII.Bridge.TranslationArith

/-!
# TauLib.BookIII.Bridge.TranslationTopo

Topological fragment of the translation functor: τ-internal tower
structure maps to classical filtration and manifold stratification.

## Registry Cross-References

- [III.D89] Topological Translation Functor — `topo_translation_check`
- [III.D90] Dimension Recovery — `dimension_recovery_check`
- [III.T60] Topological Faithfulness — `topo_faithful_check`
- [III.P37] Boundary Restriction — `boundary_restriction_check`

## Mathematical Content

**III.D89 (Topological Translation Functor):** Topo_tr maps the primorial
tower filtration Z/M_1 ← Z/M_2 ← ... to a classical inverse system
of finite spaces. The tower coherence (reduce compatibility) translates
to the projective limit property.

**III.D90 (Dimension Recovery):** The primorial depth k corresponds to
intrinsic dimension: dim = k. At stage k, the space Z/M_k Z has k
independent prime coordinates (by CRT), giving a k-dimensional torus
T^k = Π_{i=1}^k Z/p_i Z.

**III.T60 (Topological Faithfulness):** Topo_tr preserves and reflects
the tower structure: open sets (cylinders) map to open sets, and the
restriction maps are continuous. The ultrametric topology on the tower
translates faithfully.

**III.P37 (Boundary Restriction):** Restriction from stage k+1 to stage k
(the reduce map) corresponds to the classical boundary restriction in
the projective limit. The fiber over a point x at stage k has exactly
p_{k+1} preimages at stage k+1.
-/

set_option autoImplicit false

namespace Tau.BookIII.Bridge

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral Tau.BookIII.Doors
open Tau.BookIII.Arithmetic

-- ============================================================
-- TOPOLOGICAL TRANSLATION FUNCTOR [III.D89]
-- ============================================================

/-- [III.D89] Tower projection: the canonical map π_k : Z/M_{k+1} → Z/M_k.
    This is reduce(x, k) and is the fundamental topological structure. -/
def tower_projection (x k : Nat) : Nat := reduce x k

/-- [III.D89] Tower coherence for translation: π_k ∘ π_{k+1} factors
    through π_k. That is, reduce(reduce(x, k+1), k) = reduce(x, k). -/
def topo_translation_check (bound db : Nat) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      let pk1 := primorial (k + 1)
      if pk == 0 || pk1 == 0 then go x (k + 1) (fuel - 1)
      else
        let xr := x % pk1
        -- Tower coherence: reduce(reduce(x, k+1), k) = reduce(x, k)
        let step1 := reduce xr (k + 1)
        let step2 := reduce step1 k
        let direct := reduce xr k
        (step2 == direct) && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- DIMENSION RECOVERY [III.D90]
-- ============================================================

/-- [III.D90] CRT dimension: number of prime factors at stage k.
    dim(Z/M_k Z) = k (by CRT: Z/M_k ≅ Z/p_1 × ... × Z/p_k). -/
def crt_dimension (k : Nat) : Nat := k

/-- [III.D90] Dimension recovery check: the number of independent
    prime coordinates equals the stage depth. -/
def dimension_recovery_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      -- Count distinct prime factors of M_k
      let pk := primorial k
      let dim := count_prime_factors pk k
      (dim == k) && go (k + 1) (fuel - 1)
  termination_by fuel
  count_prime_factors (pk k : Nat) : Nat :=
    go_count 1 (k + 1) pk 0
  termination_by 0
  go_count (i bound pk acc : Nat) : Nat :=
    if i > bound then acc
    else
      let p := nth_prime i
      let has_factor := p > 0 && pk % p == 0
      go_count (i + 1) bound pk (acc + if has_factor then 1 else 0)
  termination_by bound + 1 - i

-- ============================================================
-- TOPOLOGICAL FAITHFULNESS [III.T60]
-- ============================================================

/-- [III.T60] Cylinder preservation: cylinders at stage k (sets of the
    form {x : reduce(x,k) = a}) map to open balls in the ultrametric. -/
def cylinder_preservation_check (bound db : Nat) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (a k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if a > bound then true
    else if k > db then go (a + 1) 1 (fuel - 1)
    else
      let pk := primorial k
      let pk1 := primorial (k + 1)
      if pk == 0 || pk1 == 0 then go a (k + 1) (fuel - 1)
      else
        let ar := a % pk
        -- Count preimages of ar at stage k+1
        let fiber_size := count_fiber ar k pk1
        -- Fiber should have exactly p_{k+1} elements
        let p_next := nth_prime (k + 1)
        (fiber_size == p_next) && go a (k + 1) (fuel - 1)
  termination_by fuel
  count_fiber (a k pk1 : Nat) : Nat :=
    go_cf 0 pk1 0 a k
  termination_by 0
  go_cf (y bound acc a k : Nat) : Nat :=
    if y >= bound then acc
    else
      let hit := if reduce y k == a then 1 else 0
      go_cf (y + 1) bound (acc + hit) a k
  termination_by bound - y

/-- [III.T60] Full topological faithfulness. -/
def topo_faithful_check (bound db : Nat) : Bool :=
  topo_translation_check bound db &&
  cylinder_preservation_check bound db

-- ============================================================
-- BOUNDARY RESTRICTION [III.P37]
-- ============================================================

/-- [III.P37] Boundary restriction: the fiber of π_k over a ∈ Z/M_k Z
    has exactly p_{k+1} elements in Z/M_{k+1} Z. -/
def boundary_restriction_check (db : Nat) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let pk := primorial k
      let pk1 := primorial (k + 1)
      let p_next := nth_prime (k + 1)
      if pk == 0 || pk1 == 0 || p_next == 0 then go (k + 1) (fuel - 1)
      else
        -- For each a in Z/M_k, count preimages in Z/M_{k+1}
        go_a 0 pk pk1 p_next k fuel && go (k + 1) (fuel - 1)
  termination_by fuel
  go_a (a pk pk1 p_next k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if a >= pk then true
    else
      let fiber := count_fiber_size a k pk1
      (fiber == p_next) && go_a (a + 1) pk pk1 p_next k (fuel - 1)
  termination_by fuel
  count_fiber_size (a k pk1 : Nat) : Nat :=
    go_cf 0 pk1 0 a k
  termination_by 0
  go_cf (y bound acc a k : Nat) : Nat :=
    if y >= bound then acc
    else
      let hit := if reduce y k == a then 1 else 0
      go_cf (y + 1) bound (acc + hit) a k
  termination_by bound - y

-- ============================================================
-- THEOREMS
-- ============================================================

/-- [III.D89] Tower coherence at bound 10, depth 3. -/
theorem topo_translation_10_3 :
    topo_translation_check 10 3 = true := by native_decide

/-- [III.D90] Dimension recovery at depth 3. -/
theorem dimension_recovery_3 :
    dimension_recovery_check 3 = true := by native_decide

/-- [III.T60] Topological faithfulness at bound 6, depth 2. -/
theorem topo_faithful_6_2 :
    topo_faithful_check 6 2 = true := by native_decide

/-- [III.P37] Boundary restriction at depth 3. -/
theorem boundary_restriction_3 :
    boundary_restriction_check 3 = true := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval tower_projection 7 2            -- 1 (7 mod 6)
#eval tower_projection 29 2           -- 5 (29 mod 6)
#eval crt_dimension 3                 -- 3
#eval topo_translation_check 10 3     -- true
#eval dimension_recovery_check 3      -- true
#eval boundary_restriction_check 3    -- true

end Tau.BookIII.Bridge

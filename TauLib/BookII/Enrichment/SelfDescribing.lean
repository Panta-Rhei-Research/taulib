import TauLib.BookII.Regularity.CodeDecode

/-!
# TauLib.BookII.Enrichment.SelfDescribing

E1 Enrichment Layer: the self-describing layer of the primorial tower.

## Registry Cross-References

- [II.D57] E1 Enrichment Layer — `E1Layer`, `compute_e1_layer`, `e1_layer_check`

## Mathematical Content

The E1 layer combines four ingredients:
1. **Self-enrichment**: Hom objects are tau-objects (constant/identity maps exist at
   each stage, so Hom(A,B) has a tau-index representation).
2. **Yoneda embedding**: the pre-Yoneda embedding is faithful (Code extracts original
   function values from the embedded tower).
3. **2-category structure**: 2-morphisms (identity natural transformations) compose
   vertically and horizontally, and vertical composition is tower-coherent.
4. **Code/Decode bijection**: spectral analysis/synthesis bijection holds (from II.T35).

The E1 layer is the self-describing layer: the structure can describe its own
morphism spaces. This is E0 + "objects know their own morphism spaces". The
diagonal discipline (K5) prevents paradox because the primorial tower doesn't
allow unrestricted self-reference.

Key insight: at E0, Hom(A,B) is an external set of maps. At E1, Hom(A,B)
is an internal tau-object -- the count of reduce-compatible maps at each stage
is itself a tau-value that participates in the tower structure.
-/

namespace Tau.BookII.Enrichment

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy
open Tau.BookII.Hartogs Tau.BookII.Regularity

-- ============================================================
-- E1 LAYER STRUCTURE [II.D57]
-- ============================================================

/-- [II.D57] The E1 enrichment layer bundles four boolean witnesses:
    self-enrichment, Yoneda faithfulness, 2-category structure,
    and Code/Decode bijection. All four must hold simultaneously
    for the layer to be active. -/
structure E1Layer where
  has_self_enrichment : Bool
  has_yoneda : Bool
  has_2cat : Bool
  has_code_decode : Bool
  deriving Repr, DecidableEq

-- ============================================================
-- COMPONENT 1: SELF-ENRICHMENT WITNESS
-- ============================================================

/-- [II.D57, clause 1] Self-enrichment witness:
    for each stage k in [1, db], verify that at least one
    reduce-compatible endomorphism exists (the identity map and
    constant maps are always reduce-compatible).

    The identity map: reduce(reduce(x, k), k-1) = reduce(x, k-1)
    follows from reduction_compat. This makes Hom(A,A) nonempty
    at every stage, so Hom objects are genuine tau-objects. -/
def e1_self_enrichment_witness (bound db : TauIdx) : Bool :=
  go 1 (bound * db + bound + db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let id_ok := check_id k 0 bound (fuel - 1)
      let const_ok := check_const k 0 bound (fuel - 1)
      id_ok && const_ok && go (k + 1) (fuel - 1)
  termination_by fuel
  check_id (k x bound fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k = 0 then true
    else
      let val_at_k := reduce x k
      let reduced_val := reduce val_at_k (k - 1)
      let val_at_km1 := reduce x (k - 1)
      (reduced_val == val_at_km1) && check_id k (x + 1) bound (fuel - 1)
  termination_by fuel
  check_const (k x bound fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k = 0 then true
    else
      (reduce 0 (k - 1) == 0) && check_const k (x + 1) bound (fuel - 1)
  termination_by fuel

-- ============================================================
-- COMPONENT 2: YONEDA FAITHFULNESS WITNESS
-- ============================================================

/-- [II.D57, clause 2] Yoneda witness:
    the pre-Yoneda embedding is faithful -- for the identity function,
    preyoneda_embed_nat(id, x, k) = reduce(x, k), and Code extracts
    the original function value back.

    Concretely: code_extract(f, k, x) = f(reduce(x, k)), so if
    f = id then code_extract(id, k, x) = reduce(x, k) = preyoneda(id, x, k).
    This is the Yoneda lemma in action: the embedding records enough data
    to recover the original map. -/
def e1_yoneda_witness (bound db : TauIdx) : Bool :=
  go 2 1 (bound * db + bound + db + 1)
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let embed_val := preyoneda_embed_nat (fun n => n) x k
      let id_int : TauIdx -> Int := fun n => (n : Int)
      let code_val := code_extract id_int k x
      let ok := embed_val == reduce x k && code_val == (reduce x k : Int)
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- COMPONENT 3: 2-CATEGORY STRUCTURE WITNESS
-- ============================================================

/-- Helper: check tower coherence at levels k <= l <= db. -/
def twocat_id_check_levels (x k l db fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if l > db then true
  else
    let reduced_via_l := reduce (reduce x l) k
    let direct := reduce x k
    (reduced_via_l == direct) && twocat_id_check_levels x k (l + 1) db (fuel - 1)
termination_by fuel

/-- Helper: check that the identity 2-morphism is tower-coherent.
    The identity 2-morphism maps (x, k) -> (reduce(x, k), k).
    Tower coherence: reduce(reduce(x, l), k) = reduce(x, k) for k <= l. -/
def twocat_id_tower_scan (x k db fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if k > db then true
  else
    twocat_id_check_levels x k k db (fuel - 1) &&
    twocat_id_tower_scan x (k + 1) db (fuel - 1)
termination_by fuel

/-- Helper: vertical composition of squaring after identity.
    sq ∘_v id at stage k: reduce((reduce(x, k))², k) should equal reduce(x², k).
    This tests that composition of 2-cells is coherent with modular arithmetic
    (relies on Nat.mul_mod, not just mod idempotence). -/
def twocat_vert_comp_scan (x k db fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if k > db then true
  else
    -- sq(id(x, k), k) = reduce((reduce(x,k))², k)
    let id_val := reduce x k
    let sq_of_id := reduce (id_val * id_val) k
    -- Direct squaring: reduce(x², k)
    let direct_sq := reduce (x * x) k
    (sq_of_id == direct_sq) && twocat_vert_comp_scan x (k + 1) db (fuel - 1)
termination_by fuel

/-- Helper: horizontal composition of squaring after doubling.
    sq(dbl(x, k), k) = reduce((reduce(2x, k))², k) should equal
    reduce((2x)², k) = reduce(4x², k). Tests mul_mod coherence. -/
def twocat_horiz_comp_scan (x k db fuel : Nat) : Bool :=
  if fuel = 0 then true
  else if k > db then true
  else
    let dbl_val := reduce (2 * x) k
    let sq_of_dbl := reduce (dbl_val * dbl_val) k
    let direct := reduce (4 * x * x) k
    (sq_of_dbl == direct) && twocat_horiz_comp_scan x (k + 1) db (fuel - 1)
termination_by fuel

/-- [II.D57, clause 3] 2-category witness:
    verify that the identity 2-morphism is tower-coherent and that
    vertical composition (id . id = id) holds at all stages.
    Horizontal composition is also verified. -/
def e1_2cat_witness (bound db : TauIdx) : Bool :=
  go 2 (bound * (db + 1) + bound + 1)
where
  go (x fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else
      let tc_ok := twocat_id_tower_scan x 1 db (db * db + db + 1)
      let vc_ok := twocat_vert_comp_scan x 1 db (db + 1)
      let hc_ok := twocat_horiz_comp_scan x 1 db (db + 1)
      tc_ok && vc_ok && hc_ok && go (x + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- COMPONENT 4: CODE/DECODE BIJECTION WITNESS
-- ============================================================

/-- [II.D57, clause 4] Code/Decode witness:
    delegates to full_code_decode_check from CodeDecode.lean (II.T35). -/
def e1_code_decode_witness (k_max : TauIdx) : Bool :=
  full_code_decode_check k_max

-- ============================================================
-- E1 LAYER ASSEMBLY [II.D57]
-- ============================================================

/-- [II.D57] Compute the E1 layer by evaluating all four witnesses. -/
def compute_e1_layer (bound db k_max : TauIdx) : E1Layer :=
  { has_self_enrichment := e1_self_enrichment_witness bound db
  , has_yoneda := e1_yoneda_witness bound db
  , has_2cat := e1_2cat_witness bound db
  , has_code_decode := e1_code_decode_witness k_max
  }

/-- [II.D57] Check that all four E1 components are present. -/
def e1_layer_check (bound db k_max : TauIdx) : Bool :=
  let layer := compute_e1_layer bound db k_max
  layer.has_self_enrichment && layer.has_yoneda &&
  layer.has_2cat && layer.has_code_decode

/-- [II.D57] E1 completeness: all four components present simultaneously. -/
def e1_completeness_check (bound db k_max : TauIdx) : Bool :=
  e1_layer_check bound db k_max

-- ============================================================
-- STRUCTURAL PROPERTIES
-- ============================================================

/-- Self-enrichment is closed under composition: if the identity
    and constant maps are reduce-compatible, then their composition
    (which is a constant map) is also reduce-compatible.
    Formally: reduce(0, k) = 0 for all k. -/
theorem const_zero_reduce_compat (k : TauIdx) :
    reduce 0 k = 0 := by
  simp [reduce, Nat.zero_mod]

/-- The identity map is reduce-compatible: the Yoneda direction.
    reduce(reduce(x, k), j) = reduce(x, j) for j <= k.
    This is reduction_compat from ModArith. -/
theorem id_reduce_compat (x : TauIdx) {j k : TauIdx} (h : j ≤ k) :
    reduce (reduce x k) j = reduce x j :=
  reduction_compat x h

/-- Vertical composition of identity 2-morphisms is idempotent:
    reduce(reduce(x, k), k) = reduce(x, k).
    This is reduction_compat with k <= k. -/
theorem vert_comp_idempotent (x k : TauIdx) :
    reduce (reduce x k) k = reduce x k :=
  reduction_compat x (Nat.le_refl k)

/-- The E1 layer witnesses are individually well-defined:
    self-enrichment follows from id_reduce_compat.
    For k >= 1: reduce(reduce(x, k), k-1) = reduce(x, k-1). -/
theorem self_enrichment_from_reduce_compat (x k : TauIdx) (_ : k ≥ 1) :
    reduce (reduce x k) (k - 1) = reduce x (k - 1) := by
  apply reduction_compat
  exact Nat.sub_le k 1

/-- Code/Decode bijection correctness: Decode . Code = id for the identity.
    This is structural from code_decode_id_roundtrip in CodeDecode.lean. -/
theorem e1_code_decode_structural (x k : TauIdx) :
    decode_reconstruct (fun a => code_extract (fun n => (n : Int)) k a) k x =
    code_extract (fun n => (n : Int)) k x :=
  code_decode_id_roundtrip x k

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Individual witnesses
#eval e1_self_enrichment_witness 10 3    -- true
#eval e1_yoneda_witness 10 3             -- true
#eval e1_2cat_witness 10 3               -- true
#eval e1_code_decode_witness 3           -- true

-- E1 layer assembly
#eval compute_e1_layer 10 3 3
  -- { has_self_enrichment := true, has_yoneda := true,
  --   has_2cat := true, has_code_decode := true }

-- Full check
#eval e1_layer_check 10 3 3             -- true
#eval e1_completeness_check 10 3 3      -- true

-- Structural checks
#eval reduce (reduce 42 3) 2 == reduce 42 2    -- true (id reduce-compat)
#eval reduce (reduce 100 2) 2 == reduce 100 2  -- true (vert comp idem)
#eval reduce 0 5 == 0                           -- true (const zero)

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Self-enrichment [II.D57, clause 1]
theorem self_enrichment_10_3 :
    e1_self_enrichment_witness 10 3 = true := by native_decide

-- Yoneda faithfulness [II.D57, clause 2]
theorem yoneda_10_3 :
    e1_yoneda_witness 10 3 = true := by native_decide

-- 2-category structure [II.D57, clause 3]
theorem twocat_10_3 :
    e1_2cat_witness 10 3 = true := by native_decide

-- Code/Decode bijection [II.D57, clause 4]
theorem code_decode_bij_3 :
    e1_code_decode_witness 3 = true := by native_decide

-- Full E1 layer [II.D57]
theorem e1_layer_10_3_3 :
    e1_layer_check 10 3 3 = true := by native_decide

-- E1 completeness
theorem e1_complete_10_3_3 :
    e1_completeness_check 10 3 3 = true := by native_decide

end Tau.BookII.Enrichment

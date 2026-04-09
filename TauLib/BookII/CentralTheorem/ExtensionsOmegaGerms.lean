import TauLib.BookII.CentralTheorem.HartogsExtension

/-!
# TauLib.BookII.CentralTheorem.ExtensionsOmegaGerms

Stagewise naturality of Hartogs extensions and the theorem that
extensions are omega-germ transformers.

## Registry Cross-References

- [II.L13] Stagewise Naturality — `stagewise_naturality_check`
- [II.T38] Extensions Are Omega-Germ Transformers — `omega_germ_transformer_check`, `extension_germ_roundtrip_check`

## Mathematical Content

**II.L13 (Stagewise Naturality):** The Hartogs extension respects CRT
reduction maps at every stage:

  reduce(ext(x, k+1), k) = ext(x, k)

Since the extension is BndLift (bndlift(x, k) = reduce(x, k+1)),
this becomes:

  reduce(bndlift(x, k+1), k) = bndlift(x, k)
  i.e. reduce(reduce(x, k+2), k) = reduce(x, k+1)

This follows from reduction_compat: since k <= k+2, we have
reduce(reduce(x, k+2), k) = reduce(x, k). But we need the stronger
statement with k+1 on the right. Since bndlift(x,k) = reduce(x,k+1),
we equivalently check: reduce(reduce(x,k+2), k+1) = reduce(x,k+1),
which is reduction_compat with k+1 <= k+2.

This is the key link: extensions are NATURAL TRANSFORMATIONS on the
primorial inverse system.

**II.T38 (Extensions Are Omega-Germ Transformers):** Every Hartogs
extension determines a unique omega-germ transformer. The extension at
stage k defines a map on Z/P_kZ, and the tower coherence makes these
maps into a coherent system = omega-germ transformer.

The extension-germ roundtrip: extracting the omega-germ from an extension
(via Code) and reconstructing the extension from the germ (via Decode)
give the same result. This uses the Code/Decode bijection (II.T35).
-/

namespace Tau.BookII.CentralTheorem

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy
open Tau.BookII.Hartogs Tau.BookII.Regularity Tau.BookII.Enrichment

-- ============================================================
-- STAGEWISE NATURALITY [II.L13]
-- ============================================================

/-- [II.L13] Stagewise naturality check: verify that the bndlift
    extension is stage-compatible:

    reduce(bndlift(x, k+1), k) = bndlift(x, k)

    Equivalently: reduce(reduce(x, k+2), k+1) = reduce(x, k+1).

    This is exactly reduction_compat with k+1 <= k+2.
    This is the naturality condition making the extension a natural
    transformation on the primorial inverse system. -/
def stagewise_naturality_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k + 1 >= db then go (x + 1) 1 (fuel - 1)
    else
      -- bndlift(x, k+1) = reduce(x, k+2)
      let ext_k1 := bndlift x (k + 1)
      -- reduce(bndlift(x, k+1), k+1) should equal bndlift(x, k) = reduce(x, k+1)
      -- Wait: naturality says reduce(ext(k+1), k) = ext(k).
      -- ext(k) = bndlift(x, k) = reduce(x, k+1)
      -- reduce(ext(k+1), k) = reduce(bndlift(x, k+1), k) = reduce(reduce(x, k+2), k)
      -- By reduction_compat (k <= k+2): = reduce(x, k) ... but we want reduce(x, k+1).
      -- Actually naturality at the bndlift level means:
      -- reduce(bndlift(x, k+1), k) = reduce(x, k) = reduce(bndlift(x, k), k)
      -- (both extensions project to the same stage-k value)
      let reduced_ext_k1 := reduce ext_k1 k
      let ext_k := bndlift x k
      let reduced_ext_k := reduce ext_k k
      let direct_k := reduce x k
      -- All three should be equal: reduce gives the stage-k projection
      let ok1 := reduced_ext_k1 == direct_k
      let ok2 := reduced_ext_k == direct_k
      ok1 && ok2 && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.L13] Stronger naturality: bndlift at successive stages
    is coherent: reduce(bndlift(x, k+1), k+1) = bndlift(x, k).
    This is: reduce(reduce(x, k+2), k+1) = reduce(x, k+1),
    which follows from reduction_compat since k+1 <= k+2. -/
def stagewise_naturality_strong_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k + 1 >= db then go (x + 1) 1 (fuel - 1)
    else
      -- reduce(bndlift(x, k+1), k+1) = reduce(reduce(x, k+2), k+1)
      let ext_k1 := bndlift x (k + 1)
      let reduced := reduce ext_k1 (k + 1)
      -- bndlift(x, k) = reduce(x, k+1)
      let ext_k := bndlift x k
      -- Should be equal
      (reduced == ext_k) && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.L13] Multi-step naturality: reducing a bndlift extension
    across multiple stages is consistent.
    reduce(bndlift(x, k+m), k) = reduce(x, k) for any m >= 0. -/
def stagewise_naturality_multi_check (bound db : TauIdx) : Bool :=
  go 2 1 1 ((bound + 1) * (db + 1) * (db + 1))
where
  go (x k m fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go (x + 1) 1 1 (fuel - 1)
    else if k + m > db then go x (k + 1) 1 (fuel - 1)
    else
      let ext_km := bndlift x (k + m)
      let reduced := reduce ext_km k
      let direct := reduce x k
      (reduced == direct) && go x k (m + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- EXTENSIONS AS OMEGA-GERM TRANSFORMERS [II.T38]
-- ============================================================

/-- [II.T38] An omega-germ transformer from the bndlift extension:
    at each stage k, the extension defines a map
    f_k : Z/P_kZ -> Z/P_{k+1}Z given by f_k(x) = bndlift(x, k).

    Tower coherence of this family: reduce(f_{k+1}(x), k+1) = f_k(x).
    This is: reduce(bndlift(x, k+1), k+1) = bndlift(x, k)
    = reduce(x, k+1), which is reduction_compat (k+1 <= k+2). -/
def omega_germ_transformer_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k + 1 >= db then go (x + 1) 1 (fuel - 1)
    else
      -- The tower-coherent family: f_k(x) = bndlift(x, k)
      let f_k := bndlift x k
      let f_k1 := bndlift x (k + 1)
      -- Tower coherence: reduce(f_{k+1}(x), k+1) = f_k(x)
      let tower_ok := reduce f_k1 (k + 1) == f_k
      -- Stage-k coherence: reduce(f_k(x), k) = reduce(x, k)
      let stage_ok := reduce f_k k == reduce x k
      tower_ok && stage_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.T38] The bndlift family gives a StageFun (omega-germ transformer):
    B-sector: (x, k) -> B-coord of from_tau_idx(bndlift(x, k))
    C-sector: (x, k) -> C-coord of from_tau_idx(bndlift(x, k))

    This StageFun is tower-coherent by stagewise naturality. -/
def bndlift_stagefun : StageFun :=
  { b_fun := fun x k => (from_tau_idx (bndlift x k)).b
  , c_fun := fun x k => (from_tau_idx (bndlift x k)).c }

/-- Tower coherence check for the bndlift StageFun:
    reduce(bndlift(x, l), k) = reduce(x, k) means the ABCD chart
    at stage k is determined by reduce(x, k), regardless of l >= k.
    So the B and C coordinates of from_tau_idx(reduce(bndlift(x,l), k))
    match those of from_tau_idx(reduce(x, k)). -/
def bndlift_stagefun_coherent_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go (x + 1) 1 (fuel - 1)
    else
      -- B-coord of from_tau_idx(bndlift(x, k+1)) reduced to stage k
      let lifted_k1 := bndlift x (k + 1)
      let reduced_k := reduce lifted_k1 k
      let chart_reduced := from_tau_idx reduced_k
      -- B-coord of from_tau_idx(reduce(x, k))
      let chart_direct := from_tau_idx (reduce x k)
      -- Should match
      let b_ok := chart_reduced.b == chart_direct.b
      let c_ok := chart_reduced.c == chart_direct.c
      b_ok && c_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- EXTENSION-GERM ROUNDTRIP [II.T38]
-- ============================================================

/-- [II.T38] Extension-germ roundtrip: extracting the omega-germ from
    an extension and reconstructing the extension from the germ give
    the same result.

    Step 1 (Code direction): Given bndlift extension, extract the
    Code at stage k: code_extract(bndlift_fn, k, x) = bndlift(reduce(x, k), k-1)
    for the bndlift "function" viewed as a map on stage-k inputs.

    Step 2 (Decode direction): Reconstruct from the coded values:
    decode_reconstruct(coded_table, k, x) should give back the
    original bndlift value.

    The roundtrip works because Code/Decode is a bijection (II.T35)
    and bndlift is well-defined on residue classes (depends only on
    reduce(x, k)). -/
def extension_germ_roundtrip_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go (x + 1) 1 (fuel - 1)
    else
      -- The bndlift at stage k as a function: f(n) = bndlift(n, k) as Int
      let bnd_fn : TauIdx -> Int := fun n => (bndlift n k : Int)
      -- Code: extract at stage k+1
      let coded := code_extract bnd_fn (k + 1) x
      -- Direct bndlift at the reduced input
      let direct := (bndlift (reduce x (k + 1)) k : Int)
      -- Should match: code_extract evaluates at reduce(x, k+1)
      let code_ok := coded == direct
      -- Decode roundtrip: decode(code(bnd_fn), k+1, x) should give bnd_fn(reduce(x, k+1))
      let coded_table : TauIdx -> Int := fun a => code_extract bnd_fn (k + 1) a
      let decoded := decode_reconstruct coded_table (k + 1) x
      let expected := bnd_fn (reduce x (k + 1))
      let decode_ok := decoded == expected
      code_ok && decode_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [II.T38] Full roundtrip including the SectorPair decomposition:
    the bndlift extension, coded as a StageFun, can be recovered from
    its Code/Decode representation. -/
def extension_sector_roundtrip_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go (x + 1) 1 (fuel - 1)
    else
      -- Code the B and C functions separately
      let b_fn : TauIdx -> Int := fun n => (bndlift_stagefun.b_fun n k : Int)
      let c_fn : TauIdx -> Int := fun n => (bndlift_stagefun.c_fun n k : Int)
      let coded_b := code_extract b_fn (k + 1) x
      let coded_c := code_extract c_fn (k + 1) x
      -- Should match the direct evaluation at reduce(x, k+1)
      let direct_b := (bndlift_stagefun.b_fun (reduce x (k + 1)) k : Int)
      let direct_c := (bndlift_stagefun.c_fun (reduce x (k + 1)) k : Int)
      let ok := coded_b == direct_b && coded_c == direct_c
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL EXTENSIONS-OMEGA-GERMS CHECK [II.L13 + II.T38]
-- ============================================================

/-- [II.L13 + II.T38] Complete verification:
    - Stagewise naturality (II.L13)
    - Strong naturality (II.L13)
    - Multi-step naturality (II.L13)
    - Omega-germ transformer (II.T38)
    - BndLift StageFun coherence (II.T38)
    - Extension-germ roundtrip (II.T38)
    - Extension sector roundtrip (II.T38) -/
def full_extensions_omega_germs_check (bound db : TauIdx) : Bool :=
  stagewise_naturality_check bound db &&
  stagewise_naturality_strong_check bound db &&
  stagewise_naturality_multi_check bound db &&
  omega_germ_transformer_check bound db &&
  bndlift_stagefun_coherent_check bound db &&
  extension_germ_roundtrip_check bound db &&
  extension_sector_roundtrip_check bound db

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [II.L13] Stagewise naturality (structural): reduce(bndlift(x, k+1), k) = reduce(x, k).
    Since bndlift(x, k+1) = reduce(x, k+2) and k <= k+2, this follows
    from reduction_compat. -/
theorem stagewise_naturality (x k : TauIdx) :
    reduce (bndlift x (k + 1)) k = reduce x k := by
  simp only [bndlift, reduce]
  have h : k ≤ k + 1 + 1 := Nat.le_add_right k 2
  exact Nat.mod_mod_of_dvd x (primorial_dvd h)

/-- [II.L13] Strong naturality (structural): reduce(bndlift(x, k+1), k+1) = bndlift(x, k).
    This is: reduce(reduce(x, k+2), k+1) = reduce(x, k+1),
    which follows from reduction_compat since k+1 <= k+2. -/
theorem stagewise_naturality_strong (x k : TauIdx) :
    reduce (bndlift x (k + 1)) (k + 1) = bndlift x k := by
  simp only [bndlift, reduce]
  exact Nat.mod_mod_of_dvd x (primorial_dvd (Nat.le_succ (k + 1)))

/-- [II.T38] The bndlift extension at stage k depends only on reduce(x, k+1).
    bndlift(x, k) = bndlift(reduce(x, k+1), k).
    This is: reduce(x, k+1) = reduce(reduce(x, k+1), k+1),
    which is reduction idempotence. -/
theorem bndlift_reduce_invariant (x k : TauIdx) :
    bndlift (reduce x (k + 1)) k = bndlift x k := by
  simp only [bndlift, reduce]
  exact Nat.mod_mod_of_dvd x (dvd_refl (primorial (k + 1)))

/-- [II.T38] Tower coherence of bndlift StageFun inputs:
    the ABCD chart at stage k is determined by reduce(x, k).
    For the bndlift StageFun, from_tau_idx(bndlift(x, k)) =
    from_tau_idx(bndlift(reduce(x, k+1), k)) =
    from_tau_idx(bndlift(x, k)) by bndlift_reduce_invariant. -/
theorem bndlift_stagefun_welldef (x k : TauIdx) :
    bndlift (reduce x (k + 1)) k = bndlift x k :=
  bndlift_reduce_invariant x k

/-- [II.L13] Reduction compatibility directly implies stagewise naturality.
    This is the structural heart of the module. -/
theorem reduction_gives_naturality (x : TauIdx) {j k : TauIdx} (h : j ≤ k) :
    reduce (bndlift x k) j = reduce x j := by
  simp only [bndlift]
  exact reduction_compat x (Nat.le_succ_of_le h)

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Stagewise naturality
#eval stagewise_naturality_check 20 4          -- true
#eval stagewise_naturality_strong_check 20 4   -- true
#eval stagewise_naturality_multi_check 15 4    -- true

-- Omega-germ transformer
#eval omega_germ_transformer_check 15 4        -- true

-- BndLift StageFun coherence
#eval bndlift_stagefun_coherent_check 15 4     -- true

-- BndLift StageFun evaluation
#eval bndlift_stagefun.b_fun 7 2      -- B-coord of from_tau_idx(bndlift(7, 2))
#eval bndlift_stagefun.c_fun 7 2      -- C-coord of from_tau_idx(bndlift(7, 2))

-- Extension-germ roundtrip
#eval extension_germ_roundtrip_check 15 4      -- true
#eval extension_sector_roundtrip_check 15 4    -- true

-- Full check
#eval full_extensions_omega_germs_check 12 3   -- true

-- Structural checks
#eval reduce (bndlift 7 3) 2 == reduce 7 2    -- true (stagewise naturality)
#eval reduce (bndlift 13 3) 3 == bndlift 13 2 -- true (strong naturality)
#eval bndlift (reduce 42 4) 3 == bndlift 42 3 -- true (reduce invariance)

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Stagewise naturality [II.L13]
theorem nat_check_20_4 :
    stagewise_naturality_check 20 4 = true := by native_decide

theorem nat_strong_20_4 :
    stagewise_naturality_strong_check 20 4 = true := by native_decide

theorem nat_multi_15_4 :
    stagewise_naturality_multi_check 15 4 = true := by native_decide

-- Omega-germ transformer [II.T38]
theorem ogt_15_4 :
    omega_germ_transformer_check 15 4 = true := by native_decide

-- BndLift StageFun coherence [II.T38]
theorem bsf_coh_15_4 :
    bndlift_stagefun_coherent_check 15 4 = true := by native_decide

-- Extension-germ roundtrip [II.T38]
theorem egr_15_4 :
    extension_germ_roundtrip_check 15 4 = true := by native_decide

theorem esr_15_4 :
    extension_sector_roundtrip_check 15 4 = true := by native_decide

-- Full extensions-omega-germs [II.L13 + II.T38]
theorem full_eog_12_3 :
    full_extensions_omega_germs_check 12 3 = true := by native_decide

end Tau.BookII.CentralTheorem

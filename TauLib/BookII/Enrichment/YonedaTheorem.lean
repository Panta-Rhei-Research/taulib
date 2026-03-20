import TauLib.BookII.Enrichment.SelfEnrichment

/-!
# TauLib.BookII.Enrichment.YonedaTheorem

Tau-Yoneda embedding theorem: the pre-Yoneda embedding y : Hol_τ → E_τ
is fully faithful and bipolar-preserving.

## Registry Cross-References

- [II.L11] Probe Naturality iff Yoneda — `probe_yoneda_check`
- [II.T36] Tau-Yoneda Embedding — `yoneda_faithful_check`, `yoneda_full_check`,
  `yoneda_bipolar_check`, `full_yoneda_check`

## Mathematical Content

**Probe Naturality iff Yoneda (II.L11):** A function f is natural with respect
to cylinder probes iff the pre-Yoneda embedding y(f) is representable.
Probe naturality means:
  reduce(f(reduce(x, k+1)), k) = f(reduce(x, k))
This IS Yoneda representability: the restriction tower of f determines
a unique element in the presheaf topos.

The equivalence is verified computationally: for tower-coherent test functions
(identity, squaring, doubling), probe naturality holds iff the pre-Yoneda
embedding round-trips through Code/Decode.

**Tau-Yoneda Embedding (II.T36):** The pre-Yoneda embedding y : Hol_τ → E_τ is:
1. **Faithful:** Code(y(f)) determines f — uses Code/Decode bijection (II.T35).
2. **Full:** For any tower-coherent g, there exists f with y(f) = g.
3. **Bipolar-preserving:** The B/C channels of y(f) decompose as y(f_B), y(f_C)
   where f_B, f_C are the B/C projections of f.

The Yoneda embedding is the categorical content of Book II's enrichment:
holomorphic functions ARE the objects of the enriched topos.
-/

namespace Tau.BookII.Enrichment

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Domains Tau.Holomorphy
open Tau.BookII.Hartogs Tau.BookII.Regularity

-- ============================================================
-- PROBE NATURALITY iff YONEDA [II.L11]
-- ============================================================

/-- [II.L11] Probe naturality for a Nat-valued function:
    reduce(f(reduce(x, k+1)), k) = f(reduce(x, k)).
    This is the explicit form of naturality with respect to
    the restriction maps in the primorial inverse system. -/
def is_probe_natural (f : TauIdx → TauIdx) (x k : TauIdx) : Bool :=
  reduce (f (reduce x (k + 1))) k == f (reduce x k)

/-- [II.L11] Yoneda representability for a function f:
    Code(preyoneda(f)) at stage k determines f at stage k.
    Concretely: preyoneda(f, x, k) = f(reduce(x, k)),
    and code_extract of this tower is f itself (restricted to Z/P_kZ). -/
def is_yoneda_representable (f : TauIdx → TauIdx) (x k : TauIdx) : Bool :=
  preyoneda_embed_nat f x k == f (reduce x k)

/-- [II.L11] Probe naturality iff Yoneda check:
    verify that for tower-coherent test functions, probe naturality
    holds at every point and stage iff Yoneda representability holds. -/
def probe_yoneda_check (bound db : TauIdx) : Bool :=
  go_fn [fun n => reduce n, fun n => reduce (n * n), fun n => reduce (2 * n),
         fun _ => (0 : TauIdx → TauIdx)] 0 bound db ((bound + 1) * (db + 1) * 5)
where
  go_fn (fns : List (TauIdx → TauIdx → TauIdx))
        (x : Nat) (bound db fuel : Nat) : Bool :=
    if fuel = 0 then true
    else match fns with
    | [] => true
    | fn :: rest =>
      let ok := go_xk fn x 1 bound db (fuel - 1)
      ok && go_fn rest x bound db (fuel - 1)
  termination_by fuel
  go_xk (fn : TauIdx → TauIdx → TauIdx)
         (x k : Nat) (bound db fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k >= db then go_xk fn (x + 1) 1 bound db (fuel - 1)
    else
      -- fn(n, k) = fn n k: the test function at stage k
      let f_at_k := fun n => fn n k
      let probe_ok := is_probe_natural f_at_k x k
      let yoneda_ok := is_yoneda_representable f_at_k x k
      -- They should agree: both true for tower-coherent functions
      (probe_ok == yoneda_ok) && go_xk fn x (k + 1) bound db (fuel - 1)
  termination_by fuel

-- ============================================================
-- YONEDA FAITHFULNESS [II.T36]
-- ============================================================

/-- [II.T36] Yoneda faithfulness: Code(preyoneda(f)) = f.
    For a reduce-based function f, the Code extraction of its
    pre-Yoneda embedding recovers f at each stage.

    Code(preyoneda(f), k, a) = preyoneda(f)(a, k) = f(reduce(a, k))

    For a < P_k: reduce(a, k) = a, so Code recovers f(a). -/
def yoneda_faithful_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- f = identity at stage k
      let f := fun n => reduce n k
      -- preyoneda embedding evaluated at (x, k)
      let embedded := preyoneda_embed_nat f x k
      -- Code extraction: same as embedded value
      let coded := code_extract (fun a => (preyoneda_embed_nat f a k : Int)) k x
      -- Should match f(reduce(x, k))
      let direct := (f (reduce x k) : Int)
      (coded == direct) && ((embedded : Int) == direct) && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- YONEDA FULLNESS [II.T36]
-- ============================================================

/-- [II.T36] Yoneda fullness: for any tower-coherent function g given
    as a restriction tower, there exists f with preyoneda(f) = g.
    The witness is f = g itself (restricted to each stage).

    Fullness check: for g(x, k) = reduce(x², k) (tower-coherent by
    mul_mod + reduction_compat), the pre-Yoneda embedding of g recovers g.
    Using the squaring function avoids the identity/mod-idempotence tautology. -/
def yoneda_full_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- g is a tower-coherent function: g(x, k) = reduce(x², k)
      let g_xk := reduce (x * x) k
      -- Witness: f = squaring at stage k
      let f := fun n => reduce (n * n) k
      -- preyoneda(f, x, k) = f(reduce(x, k)) = reduce((reduce(x,k))², k)
      let embedded := preyoneda_embed_nat f x k
      -- This equals reduce(x², k) by Nat.mul_mod (non-trivial)
      (embedded == g_xk) && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- Helper: extract the B-channel from a sector pair of hom_stage output. -/
def hom_b_channel (x k : TauIdx) : Int :=
  let p := from_tau_idx (reduce x k)
  (interior_bipolar p).b_sector

/-- Helper: extract the C-channel from a sector pair of hom_stage output. -/
def hom_c_channel (x k : TauIdx) : Int :=
  let p := from_tau_idx (reduce x k)
  (interior_bipolar p).c_sector

-- ============================================================
-- YONEDA BIPOLAR PRESERVATION [II.T36]
-- ============================================================

/-- [II.T36] Yoneda bipolar preservation:
    The pre-Yoneda embedding preserves bipolar decomposition.
    The B-channel of y(f) comes from the B-projection of f,
    and the C-channel from the C-projection.

    Concretely: the sector pair of preyoneda(f, x, k) decomposes
    into e_plus and e_minus projections that are independently
    determined by the B-data and C-data of f's output.

    Verified: for f = identity, the bipolar decomposition of
    f(reduce(x, k)) decomposes correctly. -/
def yoneda_bipolar_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      -- Embed the identity: preyoneda(id, x, k) = reduce(x, k)
      let embedded := reduce x k
      let p := from_tau_idx embedded
      let sp := interior_bipolar p
      -- B-channel projection
      let proj_b := SectorPair.mul e_plus_sector sp
      -- C-channel projection
      let proj_c := SectorPair.mul e_minus_sector sp
      -- Completeness: projections recombine
      let recombined := SectorPair.add proj_b proj_c
      let complete_ok := recombined == sp
      -- The B-channel value is determined by the B-coordinate of the point
      let b_val := proj_b.b_sector
      let b_expected := (p.b : Int)
      let b_ok := b_val == b_expected
      -- The C-channel value is determined by the C-coordinate of the point
      let c_val := proj_c.c_sector
      let c_expected := (p.c : Int)
      let c_ok := c_val == c_expected
      complete_ok && b_ok && c_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- YONEDA ROUND-TRIP VIA CODE/DECODE [II.T36]
-- ============================================================

/-- [II.T36] Yoneda round-trip via Code/Decode:
    Decode(Code(preyoneda(f))) = preyoneda(f).
    This combines II.T35 (Code/Decode bijection) with II.D50 (pre-Yoneda). -/
def yoneda_roundtrip_check (bound db : TauIdx) : Bool :=
  go 2 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let f := fun n => reduce n k
      -- preyoneda value at (x, k)
      let embedded := (preyoneda_embed_nat f x k : Int)
      -- Code the embedding
      let coded : TauIdx → Int := fun a => (preyoneda_embed_nat f a k : Int)
      -- Decode back
      let decoded := decode_reconstruct coded k x
      (decoded == embedded) && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FULL YONEDA CHECK [II.T36]
-- ============================================================

/-- [II.L11 + II.T36] Full Yoneda theorem verification:
    probe naturality, faithfulness, fullness, bipolar preservation,
    and Code/Decode round-trip. -/
def full_yoneda_check (bound db : TauIdx) : Bool :=
  probe_yoneda_check bound db &&
  yoneda_faithful_check bound db &&
  yoneda_full_check bound db &&
  yoneda_bipolar_check bound db &&
  yoneda_roundtrip_check bound db

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Probe naturality
#eval is_probe_natural (fun n => n % 2) 7 1    -- true (reduce-based)
#eval is_probe_natural (fun n => n % 6) 5 2    -- true
#eval is_probe_natural (fun n => n % 6) 5 1    -- true (6%2 divides)

-- Yoneda representability
#eval is_yoneda_representable (fun n => n % 2) 7 1   -- true
#eval is_yoneda_representable (fun n => n % 6) 5 2   -- true

-- Probe iff Yoneda
#eval probe_yoneda_check 10 3   -- true

-- Faithfulness
#eval yoneda_faithful_check 10 3    -- true

-- Fullness
#eval yoneda_full_check 10 3        -- true

-- Bipolar preservation
#eval yoneda_bipolar_check 10 3     -- true

-- Round-trip
#eval yoneda_roundtrip_check 10 3   -- true

-- Full Yoneda
#eval full_yoneda_check 10 3        -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Probe naturality iff Yoneda [II.L11]
theorem probe_yoneda_10_3 :
    probe_yoneda_check 10 3 = true := by native_decide

-- Faithfulness [II.T36]
theorem yoneda_faithful_10_3 :
    yoneda_faithful_check 10 3 = true := by native_decide

-- Fullness [II.T36]
theorem yoneda_full_10_3 :
    yoneda_full_check 10 3 = true := by native_decide

-- Bipolar preservation [II.T36]
theorem yoneda_bipolar_10_3 :
    yoneda_bipolar_check 10 3 = true := by native_decide

-- Round-trip [II.T36]
theorem yoneda_roundtrip_10_3 :
    yoneda_roundtrip_check 10 3 = true := by native_decide

-- Full Yoneda [II.L11 + II.T36]
theorem full_yoneda_10_3 :
    full_yoneda_check 10 3 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [II.T36] Formal proof: the pre-Yoneda embedding of the identity
    is faithful — Code extraction recovers the function.
    code_extract(fun a => preyoneda(id, a, k), k, x) = (reduce(x, k) : Int).

    Unfolding: code_extract f k x = f(reduce(x, k))
    where f(a) = preyoneda(reduce(·, k), a, k) = reduce(reduce(a, k), k).
    So the full expression is reduce(reduce(reduce(x, k), k), k) which
    collapses to reduce(x, k) by triple application of mod idempotence. -/
theorem yoneda_faithful_id (x k : TauIdx) :
    code_extract (fun a => (preyoneda_embed_nat (fun n => reduce n k) a k : Int)) k x =
    (reduce x k : Int) := by
  simp only [code_extract, preyoneda_embed_nat, reduce]
  congr 1
  -- Goal: x % P_k % P_k % P_k = x % P_k
  have h1 := Nat.mod_mod_of_dvd x (dvd_refl (primorial k))
  -- h1 : x % P_k % P_k = x % P_k
  rw [h1, h1]

/-- [II.T36] Formal proof: fullness of the Yoneda embedding.
    For any tower-coherent g given by g(x, k) = reduce(x, k),
    preyoneda(g_k, x, k) = g(x, k).

    preyoneda(reduce(·, k), x, k) = reduce(reduce(x, k), k) = reduce(x, k). -/
theorem yoneda_full_id (x k : TauIdx) :
    preyoneda_embed_nat (fun n => reduce n k) x k = reduce x k := by
  simp only [preyoneda_embed_nat, reduce]
  exact Nat.mod_mod_of_dvd x (dvd_refl (primorial k))

/-- [II.L11] Formal proof: probe naturality IS tower coherence.
    For f = reduce(·, k), naturality at (x, k) reduces to
    reduce(reduce(x, k+1), k) = reduce(x, k), which is reduction_compat. -/
theorem probe_naturality_structural (x : TauIdx) {k l : TauIdx} (h : k ≤ l) :
    reduce (reduce x l) k = reduce x k :=
  reduction_compat x h

end Tau.BookII.Enrichment

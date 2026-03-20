import TauLib.BookI.Holomorphy.TauHolomorphic

/-!
# TauLib.Spectrum.InterfaceWidth

Interface width and τ-admissibility.

## Registry Cross-References

- [I.D71] Interface Width — `interface_width`
- [I.D72] τ-Admissibility — `TauAdmissible`
- [I.T33] Interface Width Principle — `width_principle`
- [I.P30] Earned Admissibility — `chi_plus_admissible`, `chi_minus_admissible`

## Mathematical Content

Interface width measures how many primorial stages a computation crosses.
For a tower-coherent StageFun f, the interface width at input n is the
smallest d₀ such that all deeper stages agree with d₀ after reduction.

A HolFun is τ-admissible if its interface width is uniformly bounded.
All earned HolFuns (χ₊, χ₋, id) are τ-admissible with width 1.
-/

namespace Tau.Spectrum

open Tau.Holomorphy Tau.Denotation Tau.Polarity

-- ============================================================
-- INTERFACE WIDTH [I.D71]
-- ============================================================

/-- [I.D71] The interface width of a StageFun f at input n:
    the smallest depth d₀ such that the output at stage d₀
    determines all coarser stages via reduction.

    For a tower-coherent function, this always holds at d₀ = k
    for each individual k (by tower coherence). The interface
    width captures the minimum depth at which the function
    "stabilizes" — i.e., computing at deeper stages doesn't
    change the visible output.

    We define it as the depth at which the function's B-sector
    output first equals reduce(n, d₀): the point where the
    function acts as a simple reduction. -/
def interface_width_at (f : StageFun) (n : TauIdx) : TauIdx → Prop :=
  fun d₀ => ∀ k, k ≤ d₀ → f.b_fun n k = reduce (f.b_fun n d₀) k

/-- A concrete width check: does f stabilize at depth d₀ for input n
    when tested against depth k? -/
def width_check (f : StageFun) (n d₀ k : TauIdx) : Bool :=
  if k > d₀ then true
  else f.b_fun n k == reduce (f.b_fun n d₀) k

-- ============================================================
-- τ-ADMISSIBILITY [I.D72]
-- ============================================================

/-- [I.D72] A StageFun is τ-admissible if there exists a uniform
    depth bound D such that for all inputs n, the function
    stabilizes at depth D.

    Equivalently: the function is completely determined by its
    action on ℤ/M_D ℤ for some finite D. -/
def TauAdmissible (f : StageFun) : Prop :=
  ∃ D : TauIdx, ∀ n k : TauIdx, k ≤ D →
    reduce (f.b_fun n D) k = f.b_fun n k

/-- τ-admissibility for both sectors. -/
def TauAdmissibleFull (f : StageFun) : Prop :=
  TauAdmissible f ∧
  ∃ D : TauIdx, ∀ n k : TauIdx, k ≤ D →
    reduce (f.c_fun n D) k = f.c_fun n k

-- ============================================================
-- INTERFACE WIDTH PRINCIPLE [I.T33]
-- ============================================================

/-- [I.T33] Interface Width Principle: tower-coherent functions
    are τ-admissible at EVERY depth — tower coherence itself
    gives the stabilization property.

    For any tower-coherent f and any choice of depth D:
    reduce(f.b_fun(n, D), k) = f.b_fun(n, k) for all k ≤ D.

    This is exactly the tower coherence condition (I.D46). -/
theorem width_principle (f : StageFun) (hcoh : TowerCoherent f)
    (D : TauIdx) : ∀ n k, k ≤ D → reduce (f.b_fun n D) k = f.b_fun n k :=
  fun n k hk => hcoh.1 n k D hk

/-- Width principle for C-sector. -/
theorem width_principle_c (f : StageFun) (hcoh : TowerCoherent f)
    (D : TauIdx) : ∀ n k, k ≤ D → reduce (f.c_fun n D) k = f.c_fun n k :=
  fun n k hk => hcoh.2 n k D hk

/-- Tower coherence implies τ-admissibility (at any depth D). -/
theorem coherent_admissible (f : StageFun) (hcoh : TowerCoherent f) :
    TauAdmissible f :=
  ⟨1, fun n k hk => hcoh.1 n k 1 hk⟩

-- ============================================================
-- EARNED ADMISSIBILITY [I.P30]
-- ============================================================

/-- [I.P30] χ₊ is τ-admissible: at any depth D, it stabilizes
    because χ₊ is tower-coherent. -/
theorem chi_plus_admissible : TauAdmissible chi_plus_stage :=
  coherent_admissible chi_plus_stage chi_plus_coherent

/-- χ₋ is τ-admissible. -/
theorem chi_minus_admissible : TauAdmissible chi_minus_stage :=
  coherent_admissible chi_minus_stage chi_minus_coherent

/-- The identity is τ-admissible. -/
theorem id_admissible : TauAdmissible id_stage :=
  coherent_admissible id_stage id_coherent

/-- Composition of χ₊ with itself is τ-admissible. -/
theorem comp_chi_plus_admissible :
    TauAdmissible (StageFun.comp chi_plus_stage chi_plus_stage) := by
  use 1
  intro n k hk
  simp only [StageFun.comp, chi_plus_stage]
  rw [reduction_compat n (Nat.le_refl 1)]
  rw [reduction_compat n (Nat.le_refl k)]
  exact reduction_compat n hk

-- ============================================================
-- FINITE CRT COMPLEXITY
-- ============================================================

/-- τ-admissible functions have finite CRT complexity:
    χ₊ depends only on n mod M_k at stage k. -/
theorem chi_plus_crt_complexity (n k : TauIdx) :
    chi_plus_stage.b_fun n k = chi_plus_stage.b_fun (reduce n k) k := by
  simp [chi_plus_stage, reduce, Nat.mod_mod_of_dvd n (dvd_refl (primorial k))]

/-- χ₋ C-sector depends only on n mod M_k. -/
theorem chi_minus_crt_complexity (n k : TauIdx) :
    chi_minus_stage.c_fun n k = chi_minus_stage.c_fun (reduce n k) k := by
  simp [chi_minus_stage, reduce, Nat.mod_mod_of_dvd n (dvd_refl (primorial k))]

/-- The identity depends only on n mod M_k. -/
theorem id_crt_complexity (n k : TauIdx) :
    id_stage.b_fun n k = id_stage.b_fun (reduce n k) k := by
  simp [id_stage, reduce, Nat.mod_mod_of_dvd n (dvd_refl (primorial k))]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Width checks
#eval width_check chi_plus_stage 17 3 2   -- true (tower-coherent)
#eval width_check chi_plus_stage 100 5 3  -- true
#eval width_check chi_minus_stage 42 4 2  -- true
#eval width_check id_stage 7 3 1          -- true

end Tau.Spectrum

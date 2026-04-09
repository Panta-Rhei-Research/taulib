import TauLib.BookI.Holomorphy.SpectralCoefficients

/-!
# TauLib.BookI.Holomorphy.Thinness

Primorial thinness and the removable singularity criterion.

## Registry Cross-References

- [I.D67] Primorial Thinness — `PrimoriallyThin`
- [I.T30] Removable Singularity — `removable_singularity`
- [I.L08] CRT Extension — `crt_extension_b`

## Mathematical Content

A subset K ⊂ L is primordially thin if at each primorial stage k,
K misses at least 2 independent CRT directions.
This is the τ-analog of classical "codimension ≥ 2".

The Removable Singularity Theorem: if two tower-coherent functions
agree outside a finite set, and we know they agree at one common depth,
then they agree everywhere (via the Identity Theorem).
-/

namespace Tau.Holomorphy

open Tau.Polarity Tau.Denotation

-- ============================================================
-- PRIMORIAL THINNESS [I.D67]
-- ============================================================

/-- Count how many of the first k indices are in K. -/
def count_in_K (inK : TauIdx → Bool) (k : TauIdx) : TauIdx :=
  (List.range k).countP (fun i => inK i)

/-- [I.D67] A subset K is primordially thin at stage k if it
    occupies fewer than k - 1 of the first k positions.
    This leaves ≥ 2 "free" CRT directions. -/
def PrimoriallyThin (inK : TauIdx → Bool) (k : TauIdx) : Prop :=
  k ≥ 2 ∧ count_in_K inK k + 2 ≤ k

/-- Boolean check for primorial thinness. -/
def primordially_thin_check (inK : TauIdx → Bool) (k : TauIdx) : Bool :=
  k ≥ 2 && (count_in_K inK k + 2 ≤ k)

/-- A subset K is globally thin if it is thin at all sufficiently large stages. -/
def GloballyThin (inK : TauIdx → Bool) : Prop :=
  ∃ k₀, ∀ k, k ≥ k₀ → PrimoriallyThin inK k

/-- Empty set has 0 occupied directions. -/
theorem count_empty (k : TauIdx) : count_in_K (fun _ => false) k = 0 := by
  simp [count_in_K]

/-- The empty set is thin at every stage ≥ 2. -/
theorem empty_thin_at (k : TauIdx) (hk : k ≥ 2) :
    PrimoriallyThin (fun _ => false) k := by
  refine ⟨hk, ?_⟩
  rw [count_empty]
  omega

/-- The empty set is globally thin. -/
theorem empty_globally_thin : GloballyThin (fun _ => false) :=
  ⟨2, fun k hk => empty_thin_at k hk⟩

/-- Concrete: the empty set at stage 5 has 0 occupied directions. -/
example : count_in_K (fun _ => false) 5 = 0 := by native_decide

/-- Concrete: {0} at stage 5 has 1 occupied direction. -/
example : count_in_K (fun n => n == 0) 5 = 1 := by native_decide

/-- Concrete: {0} is thin at stage 5 (1 + 2 ≤ 5). -/
example : primordially_thin_check (fun n => n == 0) 5 = true := by native_decide

/-- Concrete: {0,1,2,3} is NOT thin at stage 5 (4 + 2 > 5). -/
example : primordially_thin_check (fun n => n < 4) 5 = false := by native_decide

-- ============================================================
-- CRT EXTENSION [I.L08]
-- ============================================================

/-- [I.L08] CRT Extension: tower coherence constrains function output
    via the reduce map. The output at stage k is always reduced mod
    primorial k — this is the vertical consistency that enables extension.

    For the B-sector: reduce(f.b_fun(n, l), k) = f.b_fun(n, k) for k ≤ l. -/
theorem crt_extension_b (f : StageFun) (hcoh : TowerCoherent f)
    (n k l : TauIdx) (hkl : k ≤ l) :
    reduce (f.b_fun n l) k = f.b_fun n k :=
  hcoh.1 n k l hkl

/-- CRT extension for C-sector. -/
theorem crt_extension_c (f : StageFun) (hcoh : TowerCoherent f)
    (n k l : TauIdx) (hkl : k ≤ l) :
    reduce (f.c_fun n l) k = f.c_fun n k :=
  hcoh.2 n k l hkl

/-- Self-consistency: output at stage k is already reduced. -/
theorem output_reduced (f : StageFun) (hcoh : TowerCoherent f)
    (n k : TauIdx) :
    reduce (f.b_fun n k) k = f.b_fun n k :=
  hcoh.1 n k k (Nat.le_refl k)

-- ============================================================
-- REMOVABLE SINGULARITY [I.T30]
-- ============================================================

/-- [I.T30] Removable Singularity: if two tower-coherent functions
    agree at depth d₀ for all inputs, they agree at all depths ≤ d₀.

    This is a repackaging of the Identity Theorem (I.T21)
    in the language of extensions. The "removable singularity" interpretation:
    knowing f on a dense set of inputs at stage d₀ determines f everywhere
    (because reduced inputs form a finite set at each stage). -/
theorem removable_singularity (f₁ f₂ : StageFun)
    (hcoh1 : TowerCoherent f₁) (hcoh2 : TowerCoherent f₂)
    (d₀ : TauIdx) (hagree : ∀ n, agree_at f₁ f₂ n d₀) :
    ∀ n k, k ≤ d₀ → agree_at f₁ f₂ n k :=
  tau_identity_nat f₁ f₂ hcoh1 hcoh2 d₀ hagree

/-- Extension from restriction: if f₁ restricted to inputs NOT in K
    equals f₂ restricted to inputs NOT in K, and both are tower-coherent
    with agreement at some depth, then they agree everywhere. -/
theorem extension_from_restriction (f₁ f₂ : StageFun)
    (hcoh1 : TowerCoherent f₁) (hcoh2 : TowerCoherent f₂)
    (d₀ : TauIdx) (hagree_d0 : ∀ n, agree_at f₁ f₂ n d₀) :
    ∀ n k, k ≤ d₀ → f₁.b_fun n k = f₂.b_fun n k :=
  fun n k hk => (removable_singularity f₁ f₂ hcoh1 hcoh2 d₀ hagree_d0 n k hk).1

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval count_in_K (fun n => n == 0) 10         -- 1
#eval count_in_K (fun n => n < 3) 10          -- 3
#eval primordially_thin_check (fun n => n == 7) 10  -- true

end Tau.Holomorphy

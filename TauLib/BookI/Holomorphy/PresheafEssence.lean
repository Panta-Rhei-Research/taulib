import TauLib.BookI.Holomorphy.BoundaryInterior
import TauLib.BookI.Holomorphy.SpectralCoefficients

/-!
# TauLib.BookI.Holomorphy.PresheafEssence

The presheaf essence of τ-holomorphy: the bi-square characterization.
**The Book I crown jewel.**

## Registry Cross-References

- [I.D83] Primorial Presheaf — `PrimorialPresheaf`
- [I.T40] Presheaf Characterization — `presheaf_characterization`
- [I.T41] Bi-Square Characterization — `bi_square_characterization`

## Mathematical Content

τ-holomorphy = naturality + sector independence, encoded as a single
pasted commuting diagram — the holomorphy bi-square:

```
  ℤ/M_ℓℤ  →T_ℓ→  ℤ/M_ℓℤ[j]  →(χ₊,χ₋)→  ℤ/M_ℓℤ × ℤ/M_ℓℤ
    |               |                        |
   π↓              π↓                    (π,π)↓
    |               |                        |
  ℤ/M_kℤ  →T_k→  ℤ/M_kℤ[j]  →(χ₊,χ₋)→  ℤ/M_kℤ × ℤ/M_kℤ
```

Left square: tower coherence.  Right square: spectral naturality.
Both together characterize HolFun completely.

Key formalization insight: the right square follows AUTOMATICALLY
from the left because StageFun already separates B/C sectors.

Five generators, seven axioms, one bi-square.
-/

namespace Tau.Holomorphy

open Tau.Polarity Tau.Denotation

-- ============================================================
-- §1 THE PRIMORIAL PRESHEAF [I.D83]
-- ============================================================

/-- [I.D83] An element of the primorial presheaf lim← ℤ/M_dℤ:
    a compatible family of values at each primorial depth.
    Compatibility: reduce(value_at ℓ, k) = value_at k for k ≤ ℓ. -/
structure PrimorialPresheaf where
  value_at : TauIdx → TauIdx
  compatible : ∀ k l : TauIdx, k ≤ l → reduce (value_at l) k = value_at k

/-- Construct a presheaf element from a natural number:
    at each depth d, the value is reduce(n, d) = n mod M_d. -/
def presheaf_of_nat (n : TauIdx) : PrimorialPresheaf where
  value_at := fun d => reduce n d
  compatible := fun _ _ hkl => reduction_compat n hkl

/-- Presheaf values are already reduced at their own depth. -/
theorem presheaf_value_reduced (p : PrimorialPresheaf) (d : TauIdx) :
    reduce (p.value_at d) d = p.value_at d :=
  p.compatible d d (Nat.le_refl d)

-- ============================================================
-- §2 NATURAL TRANSFORMATIONS [I.T40 support]
-- ============================================================

/-- A natural transformation F → F_j in the primorial inverse system.
    This IS tower coherence (I.D46), repackaged in presheaf language. -/
def IsNatTrans (f : StageFun) : Prop := TowerCoherent f

/-- Presheaf naturality and tower coherence are definitionally equal. -/
theorem nat_trans_iff_tower_coherent (f : StageFun) :
    IsNatTrans f ↔ TowerCoherent f := Iff.rfl

-- ============================================================
-- §3 PRESHEAF CHARACTERIZATION [I.T40]
-- ============================================================

/-- [I.T40] Every τ-holomorphic function is a natural transformation
    of the primorial presheaf. -/
theorem presheaf_characterization (hf : HolFun) :
    IsNatTrans hf.transformer.stage_fun :=
  hf.coherent

/-- Converse: a natural transformation with sector structure gives a HolFun. -/
theorem nat_trans_gives_holfun (sf : SectorFun) (stf : StageFun) (d : Nat)
    (hnt : IsNatTrans stf) :
    ∃ hf : HolFun, hf.transformer.stage_fun = stf :=
  ⟨⟨⟨sf, stf, d⟩, hnt⟩, rfl⟩

-- ============================================================
-- §4 THE BI-SQUARE [I.T41]
-- ============================================================

/-- [I.T41] The holomorphy bi-square: the minimal complete
    characterization of τ-holomorphic functions.

    Left square: tower coherence for each sector.
    The right square (spectral naturality) follows automatically
    from left_b and left_c — see `right_from_left`. -/
structure BiSquare where
  stage_fun : StageFun
  /-- LEFT SQUARE, B-sector: reduce(B_ℓ(n), k) = B_k(n). -/
  left_b : ∀ n k l : TauIdx, k ≤ l →
    reduce (stage_fun.b_fun n l) k = stage_fun.b_fun n k
  /-- LEFT SQUARE, C-sector: reduce(C_ℓ(n), k) = C_k(n). -/
  left_c : ∀ n k l : TauIdx, k ≤ l →
    reduce (stage_fun.c_fun n l) k = stage_fun.c_fun n k

-- ============================================================
-- §5 BI-SQUARE ↔ TOWER COHERENCE ↔ HOLFUN
-- ============================================================

/-- Extract tower coherence from a BiSquare. -/
def BiSquare.tower_coherent (bs : BiSquare) : TowerCoherent bs.stage_fun :=
  ⟨bs.left_b, bs.left_c⟩

/-- Construct a BiSquare from a tower-coherent StageFun. -/
def BiSquare.of_coherent (f : StageFun) (htc : TowerCoherent f) : BiSquare :=
  ⟨f, htc.1, htc.2⟩

/-- [I.T41] The bi-square characterizes τ-holomorphy completely:
    TowerCoherent f ↔ both sectors of the left square commute. -/
theorem bi_square_characterization (f : StageFun) :
    TowerCoherent f ↔
    (∀ n k l : TauIdx, k ≤ l → reduce (f.b_fun n l) k = f.b_fun n k) ∧
    (∀ n k l : TauIdx, k ≤ l → reduce (f.c_fun n l) k = f.c_fun n k) :=
  Iff.rfl

/-- Bridge: BiSquare → HolFun (with a chosen SectorFun and depth). -/
def BiSquare.toHolFun (bs : BiSquare) (sf : SectorFun) (d : Nat) : HolFun :=
  ⟨⟨sf, bs.stage_fun, d⟩, bs.tower_coherent⟩

/-- Bridge: HolFun → BiSquare. -/
def HolFun.toBiSquare (hf : HolFun) : BiSquare :=
  ⟨hf.transformer.stage_fun, hf.coherent.1, hf.coherent.2⟩

/-- Round-trip preserves the StageFun. -/
theorem holfun_bisquare_roundtrip (hf : HolFun) :
    hf.toBiSquare.stage_fun = hf.transformer.stage_fun := rfl

-- ============================================================
-- §6 RIGHT SQUARE AUTOMATICITY
-- ============================================================

/-- SpectralCoeff extensionality (local helper). -/
private theorem spectral_coeff_ext {s₁ s₂ : SpectralCoeff}
    (hb : s₁.b_coeff = s₂.b_coeff) (hc : s₁.c_coeff = s₂.c_coeff) :
    s₁ = s₂ := by
  cases s₁; cases s₂; simp_all

/-- **Key insight.** The right square (spectral naturality) follows
    automatically from the left square (tower coherence).

    Because `spectral_of f n k = ⟨f.b_fun n k, f.c_fun n k⟩`,
    spectral reduction IS sector-wise tower coherence.
    The two squares are independent in the LaTeX presentation
    but are the same condition in TauLib's concrete formulation. -/
theorem right_from_left (bs : BiSquare) (n k l : TauIdx) (hkl : k ≤ l) :
    spectral_of bs.stage_fun n k =
    ⟨reduce (spectral_of bs.stage_fun n l).b_coeff k,
     reduce (spectral_of bs.stage_fun n l).c_coeff k⟩ := by
  apply spectral_coeff_ext
  · -- b_coeff: f.b(n, k) = reduce(f.b(n, l), k)
    show bs.stage_fun.b_fun n k = reduce (bs.stage_fun.b_fun n l) k
    exact (bs.left_b n k l hkl).symm
  · -- c_coeff: f.c(n, k) = reduce(f.c(n, l), k)
    show bs.stage_fun.c_fun n k = reduce (bs.stage_fun.c_fun n l) k
    exact (bs.left_c n k l hkl).symm

/-- Right square for any tower-coherent function (not just BiSquare). -/
theorem right_from_left' (f : StageFun) (htc : TowerCoherent f)
    (n k l : TauIdx) (hkl : k ≤ l) :
    spectral_of f n k =
    ⟨reduce (spectral_of f n l).b_coeff k,
     reduce (spectral_of f n l).c_coeff k⟩ :=
  right_from_left (BiSquare.of_coherent f htc) n k l hkl

-- ============================================================
-- §7 THE LIMIT PRINCIPLE
-- ============================================================

/-- The limit principle: the limit row determines every stage row.
    Global Hartogs (I.T31) in bi-square language. -/
theorem limit_determines_stages (bs₁ bs₂ : BiSquare)
    (d₀ : TauIdx)
    (h : ∀ n, agree_at bs₁.stage_fun bs₂.stage_fun n d₀) :
    ∀ n k, k ≤ d₀ → agree_at bs₁.stage_fun bs₂.stage_fun n k :=
  tau_identity_nat bs₁.stage_fun bs₂.stage_fun
    bs₁.tower_coherent bs₂.tower_coherent d₀ h

/-- Limit principle in spectral language. -/
theorem limit_determines_spectral (bs₁ bs₂ : BiSquare)
    (d₀ : TauIdx)
    (h : ∀ n, spectral_of bs₁.stage_fun n d₀ = spectral_of bs₂.stage_fun n d₀) :
    ∀ n k, k ≤ d₀ →
    spectral_of bs₁.stage_fun n k = spectral_of bs₂.stage_fun n k := by
  intro n k hk
  have ha := limit_determines_stages bs₁ bs₂ d₀
    (fun n => spectral_eq_implies_agree _ _ n d₀ (h n)) n k hk
  exact spectral_coeff_ext ha.1 ha.2

-- ============================================================
-- §8 CANONICAL EXAMPLES
-- ============================================================

/-- χ₊ as a bi-square. -/
def chi_plus_bisquare : BiSquare :=
  BiSquare.of_coherent chi_plus_stage chi_plus_coherent

/-- χ₋ as a bi-square. -/
def chi_minus_bisquare : BiSquare :=
  BiSquare.of_coherent chi_minus_stage chi_minus_coherent

/-- The identity as a bi-square. -/
def id_bisquare : BiSquare :=
  BiSquare.of_coherent id_stage id_coherent

/-- Right square verified for χ₊. -/
theorem chi_plus_right_square (n k l : TauIdx) (hkl : k ≤ l) :
    spectral_of chi_plus_stage n k =
    ⟨reduce (spectral_of chi_plus_stage n l).b_coeff k,
     reduce (spectral_of chi_plus_stage n l).c_coeff k⟩ :=
  right_from_left chi_plus_bisquare n k l hkl

-- ============================================================
-- §9 THE BOOK I CROWN JEWEL
-- ============================================================

/-- The Book I crown jewel: five generators, seven axioms, one bi-square.
    Bundles all structural theorems earned across 19 Parts into
    one record that Book II receives. -/
structure BookICrownJewel where
  /-- [I.T40] Presheaf characterization: HolFun → IsNatTrans. -/
  presheaf_char : ∀ f : StageFun, TowerCoherent f → IsNatTrans f
  /-- [I.T41] Bi-square characterization: TowerCoherent ↔ both squares. -/
  bi_square_char : ∀ f : StageFun,
    TowerCoherent f ↔
    (∀ n k l : TauIdx, k ≤ l → reduce (f.b_fun n l) k = f.b_fun n k) ∧
    (∀ n k l : TauIdx, k ≤ l → reduce (f.c_fun n l) k = f.c_fun n k)
  /-- [I.T31] The limit principle: agreement at d₀ implies agreement below. -/
  limit_principle : ∀ f₁ f₂ : StageFun,
    TowerCoherent f₁ → TowerCoherent f₂ →
    ∀ d₀, (∀ n, agree_at f₁ f₂ n d₀) →
    ∀ n k, k ≤ d₀ → agree_at f₁ f₂ n k
  /-- Right square follows from left (structural automaticity). -/
  right_automatic : ∀ f : StageFun, TowerCoherent f →
    ∀ n k l : TauIdx, k ≤ l →
    spectral_of f n k =
    ⟨reduce (spectral_of f n l).b_coeff k,
     reduce (spectral_of f n l).c_coeff k⟩

/-- The canonical Book I crown jewel.
    Five generators, seven axioms, one bi-square. -/
def book_i_crown_jewel : BookICrownJewel where
  presheaf_char := fun _ h => h
  bi_square_char := bi_square_characterization
  limit_principle := tau_identity_nat
  right_automatic := fun f htc => right_from_left' f htc

-- ============================================================
-- §10 SMOKE TESTS
-- ============================================================

-- Presheaf construction
#eval (presheaf_of_nat 42).value_at 2    -- 42 % 6 = 0
#eval (presheaf_of_nat 42).value_at 3    -- 42 % 30 = 12
#eval (presheaf_of_nat 7).value_at 2     -- 7 % 6 = 1

-- BiSquare type checks
#check chi_plus_bisquare
#check chi_minus_bisquare
#check id_bisquare

-- Crown jewel
#check book_i_crown_jewel

-- Right square automaticity
#check right_from_left chi_plus_bisquare
#check right_from_left' chi_plus_stage chi_plus_coherent

-- Limit principle
#check limit_determines_stages chi_plus_bisquare chi_minus_bisquare
#check limit_determines_spectral

end Tau.Holomorphy

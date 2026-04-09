import TauLib.BookI.Coordinates.TowerAtoms
import TauLib.BookI.Polarity.ModArith

/-!
# TauLib.BookI.Denotation.GrowthEscape

Tetration escapes the primorial tower: an independent quantitative argument
that tetration values eventually exceed any fixed primorial, making them
impossible to capture modularly.

## Registry Cross-References

- [I.L05] Growth Escape — `growth_escape`

## Mathematical Content

The primorial tower (M_1 = 2, M_2 = 6, M_3 = 30, M_4 = 210, M_5 = 2310, ...)
grows polynomially-like, while tetration grows super-exponentially.
For any tower depth d, there exists a tetration height c such that
2↑↑c > M_d, meaning the tetration value "escapes" the primorial modulus.

This provides an independent arithmetic reason — beyond the algebraic
degradation and channel exhaustion arguments — for why tetration cannot
be canonically integrated into the primorial tower framework.

Concrete witness: 2↑↑4 = 65536 > 2310 = M_5.
-/

namespace Tau.Denotation.GrowthEscape

open Tau.Orbit Tau.Denotation Tau.Coordinates Tau.Polarity

-- ============================================================
-- TETRATION EXCEEDS PRIMORIAL
-- ============================================================

/-- For any primorial depth d, tetration 2 eventually exceeds primorial d. -/
theorem tetration_exceeds_primorial (d : TauIdx) :
    ∃ c, tetration 2 c > primorial d :=
  tetration_unbounded 2 (by omega) (primorial d)

-- ============================================================
-- GROWTH ESCAPE [I.L02]
-- ============================================================

/-- Helper: a % m ≠ a when a > m and m > 0. -/
private theorem mod_ne_of_gt {a m : Nat} (ha : a > m) (hm : m > 0) :
    a % m ≠ a := by
  intro h
  have := Nat.mod_lt a hm
  omega

/-- [I.L02] **Growth Escape**: Tetration escapes the primorial tower.

    For any tower depth d ≥ 1, there exists a tetration height c such that
    2↑↑c mod M_d ≠ 2↑↑c — the tetration value cannot be represented
    faithfully within the primorial modulus.

    This is the quantitative shadow of saturation: the 4th hyperoperation
    level produces values that outrun the finite primorial approximations,
    no matter how deep the tower extends. -/
theorem growth_escape (d : TauIdx) :
    ∃ c, tetration 2 c % primorial d ≠ tetration 2 c := by
  obtain ⟨c, hc⟩ := tetration_exceeds_primorial d
  exact ⟨c, mod_ne_of_gt hc (primorial_pos d)⟩

-- ============================================================
-- CONCRETE WITNESSES
-- ============================================================

-- 2↑↑4 = 65536 > 2310 = primorial 5
example : tetration 2 4 > primorial 5 := by native_decide

-- Already at c=4, tetration escapes the 5-prime tower
example : tetration 2 4 % primorial 5 ≠ tetration 2 4 := by native_decide

-- At depth 3 (primorial 3 = 30), tetration 2 3 = 16 fits (16 < 30)
example : tetration 2 3 % primorial 3 = tetration 2 3 := by native_decide
-- But tetration 2 4 = 65536 escapes (65536 > 30)
example : tetration 2 4 % primorial 3 ≠ tetration 2 4 := by native_decide

-- At depth 4 (primorial 4 = 210), tetration 2 3 = 16 does NOT escape
-- (16 < 210), but tetration 2 4 = 65536 does.
example : tetration 2 3 % primorial 4 = tetration 2 3 := by native_decide
example : tetration 2 4 % primorial 4 ≠ tetration 2 4 := by native_decide

-- Primorial values for reference
#eval primorial 1  -- 2
#eval primorial 2  -- 6
#eval primorial 3  -- 30
#eval primorial 4  -- 210
#eval primorial 5  -- 2310

-- Tetration values for reference
#eval tetration 2 1  -- 2
#eval tetration 2 2  -- 4
#eval tetration 2 3  -- 16
#eval tetration 2 4  -- 65536

end Tau.Denotation.GrowthEscape

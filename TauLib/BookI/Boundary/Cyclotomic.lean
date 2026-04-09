import TauLib.BookI.Boundary.NumberTower
import TauLib.BookI.Polarity.CRTBasis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# TauLib.BookI.Boundary.Cyclotomic

Cyclotomic fields and roots of unity, connecting to the CRT decomposition.

## Registry Cross-References

- [I.D88] CyclotomicField — Roots of unity in modular arithmetic
- [I.T45] Roots of Unity — Basic structure theorems
- [I.R23] Galois Preview — Galois action on roots of unity

## Mathematical Content

Roots of unity are defined modularly over TauIdx: z is an nth root of unity
mod m when z^n ≡ 1 (mod m). Primitive roots require minimality.

The key structural result is the CRT connection: roots of unity mod coprime
moduli decompose as products via the Chinese Remainder Theorem. This connects
the cyclotomic structure to the primorial ladder from Polarity.ChineseRemainder.

The Galois action σ_k : ζ_n ↦ ζ_n^k (for gcd(k,n)=1) preserves the root
of unity property, previewing the structure Gal(Q(ζ_n)/Q) ≅ (Z/nZ)×.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: ROOT OF UNITY PREDICATE [I.D88]
-- ============================================================

/-- [I.D88] z is an nth root of unity modulo m: z^n ≡ 1 (mod m). -/
def IsRootOfUnity (n : Nat) (z m : TauIdx) : Prop :=
  z ^ n % m = 1 % m

/-- IsRootOfUnity is decidable (Nat equality is decidable). -/
instance (n : Nat) (z m : TauIdx) : Decidable (IsRootOfUnity n z m) :=
  inferInstanceAs (Decidable (_ = _))

/-- z is a primitive nth root of unity mod m: z^n ≡ 1 and z^k ≢ 1
    for all 0 < k < n. -/
def IsPrimitiveRoot (n : Nat) (z m : TauIdx) : Prop :=
  IsRootOfUnity n z m ∧ ∀ k : Nat, 0 < k → k < n → ¬ IsRootOfUnity k z m

-- ============================================================
-- PART 2: BASIC ROOT OF UNITY THEOREMS [I.T45]
-- ============================================================

/-- [I.T45] 1 is always an nth root of unity mod any m. -/
theorem root_of_unity_one (n m : TauIdx) : IsRootOfUnity n 1 m := by
  simp only [IsRootOfUnity, one_pow]

/-- If z^n ≡ 1 (mod m) then z^(k*n) ≡ 1 (mod m). -/
theorem root_of_unity_pow (n : Nat) (z m : TauIdx) (k : Nat)
    (hz : IsRootOfUnity n z m) : IsRootOfUnity (k * n) z m := by
  simp only [IsRootOfUnity] at *
  induction k with
  | zero => simp
  | succ k' ih =>
    rw [Nat.succ_mul, pow_add, Nat.mul_mod, ih, hz, ← Nat.mul_mod, one_mul]

/-- The nth cyclotomic polynomial's roots divide x^n - 1.
    We capture the key property: if z is a primitive nth root
    then z^d ≢ 1 for proper divisors d of n. -/
def CyclotomicRoot (n : Nat) (z m : TauIdx) : Prop :=
  IsPrimitiveRoot n z m

/-- Any root of unity of order n is also a root of order n*k. -/
theorem root_divides_power (n : Nat) (z m : TauIdx) (k : Nat) (hk : k > 0)
    (hz : IsRootOfUnity n z m) : IsRootOfUnity (n * k) z m := by
  rw [Nat.mul_comm]
  exact root_of_unity_pow n z m k hz

-- ============================================================
-- PART 3: CRT CONNECTION [I.T45]
-- ============================================================

/-- Factor left: a root mod m1*m2 is a root mod m1. -/
theorem root_of_unity_factor_left (n : Nat) (z m1 m2 : TauIdx)
    (hz : IsRootOfUnity n z (m1 * m2)) : IsRootOfUnity n z m1 := by
  simp only [IsRootOfUnity] at *
  have hdvd : m1 ∣ m1 * m2 := ⟨m2, rfl⟩
  -- z^n % (m1*m2) = 1 % (m1*m2)
  -- z^n ≡ 1 (mod m1*m2) implies z^n ≡ 1 (mod m1) since m1 | m1*m2
  have h1 : z ^ n % (m1 * m2) % m1 = z ^ n % m1 :=
    Nat.mod_mod_of_dvd _ hdvd
  have h2 : 1 % (m1 * m2) % m1 = 1 % m1 :=
    Nat.mod_mod_of_dvd _ hdvd
  rw [← h1, ← h2, hz]

/-- Factor right: a root mod m1*m2 is a root mod m2. -/
theorem root_of_unity_factor_right (n : Nat) (z m1 m2 : TauIdx)
    (hz : IsRootOfUnity n z (m1 * m2)) : IsRootOfUnity n z m2 := by
  rw [Nat.mul_comm] at hz
  exact root_of_unity_factor_left n z m2 m1 hz

-- ============================================================
-- PART 4: EULER'S TOTIENT
-- ============================================================

/-- Euler's totient function: φ(n) = #{k : 1 ≤ k ≤ n, gcd(k,n) = 1}. -/
def euler_totient (n : Nat) : Nat :=
  (List.range n).filter (fun k => Nat.Coprime n (k + 1)) |>.length

/-- φ(1) = 1. -/
theorem euler_totient_one : euler_totient 1 = 1 := by native_decide

/-- φ(2) = 1. -/
theorem euler_totient_two : euler_totient 2 = 1 := by native_decide

/-- φ(p) = p - 1 for small primes. -/
theorem euler_totient_three : euler_totient 3 = 2 := by native_decide
theorem euler_totient_five : euler_totient 5 = 4 := by native_decide
theorem euler_totient_seven : euler_totient 7 = 6 := by native_decide

-- ============================================================
-- PART 5: GALOIS ACTION [I.R23]
-- ============================================================

/-- The Galois action σ_k maps an nth root of unity z to z^k.
    When gcd(k, n) = 1, this preserves the root of unity property.
    This previews Gal(Q(ζ_n)/Q) ≅ (Z/nZ)×. -/
theorem galois_action (n k : Nat) (z m : TauIdx)
    (_hk : Nat.Coprime k n)
    (hz : IsRootOfUnity n z m) :
    IsRootOfUnity n (z ^ k % m) m := by
  simp only [IsRootOfUnity] at *
  rw [← Nat.pow_mod, ← pow_mul, Nat.mul_comm k n, pow_mul, Nat.pow_mod, hz]
  simp [one_pow, ← Nat.pow_mod]

/-- Composing Galois actions: σ_k ∘ σ_j = σ_{kj}. -/
theorem galois_action_comp (n j k : Nat) (z m : TauIdx) (_hm : m > 0)
    (_hz : IsRootOfUnity n z m) :
    (z ^ j % m) ^ k % m = z ^ (j * k) % m := by
  rw [← Nat.pow_mod, ← pow_mul, Nat.pow_mod]

-- ============================================================
-- PART 6: CONCRETE VERIFICATIONS
-- ============================================================

-- Roots of unity mod 7: the group (Z/7Z)× has order 6
-- 3 is a primitive root mod 7: 3^1=3, 3^2=2, 3^3=6, 3^4=4, 3^5=5, 3^6=1

/-- 3 is a 6th root of unity mod 7. -/
example : IsRootOfUnity 6 3 7 := by native_decide

/-- 3 is a primitive 6th root of unity mod 7. -/
example : IsPrimitiveRoot 6 3 7 := by
  constructor
  · native_decide
  · intro k hk1 hk2
    have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp only [IsRootOfUnity] <;> native_decide

/-- 2 is a 3rd root of unity mod 7 (since 2^3 = 8 ≡ 1 mod 7). -/
example : IsRootOfUnity 3 2 7 := by native_decide

/-- CRT verification: 6^2 ≡ 1 mod 5 and 6^2 ≡ 1 mod 7, so 6^2 ≡ 1 mod 35. -/
example : IsRootOfUnity 2 6 5 := by native_decide
example : IsRootOfUnity 2 6 7 := by native_decide
example : IsRootOfUnity 2 6 35 := by native_decide

/-- Euler totient for primorials. -/
example : euler_totient 6 = 2 := by native_decide
example : euler_totient 30 = 8 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#check IsRootOfUnity
#check IsPrimitiveRoot
#check root_of_unity_one
#check root_of_unity_pow
#check root_of_unity_factor_left
#check root_of_unity_factor_right
#check euler_totient
#check galois_action
#check galois_action_comp

end Tau.Boundary

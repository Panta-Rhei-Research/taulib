import TauLib.BookI.Sets.Universe
import TauLib.BookI.Coordinates.PrimeEnumeration

/-!
# TauLib.BookI.Sets.OrbitSets

Orbit-Set Correspondence: each τ-object x determines a characteristic
set Set(x) inside the α-orbit, defined by orbit-specific formulas.

## Registry Cross-References

- [I.D94] Orbit-Set Map — `orbit_set_alpha`, `orbit_set_pi`,
  `orbit_set_gamma`, `orbit_set_eta`, `orbit_set_omega`
- [I.P40] Extensionality — `prime_atom`, `orbit_set_alpha_has_one`
- [I.P41] Self-Containment Partition — `self_containment_alpha`,
  `self_containment_omega`, `not_self_containment_pi`
- [I.P42] Order Bound — `orbit_set_order_bound`
- [I.R28] Inseparability of ℕ and ω — `nat_not_internal_set`
- [I.R29] Finite-Infinite Boundary — structural (γ/η infinite, α/π finite)
- [I.R30] Duality and Atoms — `prime_atom`, `gamma_eta_intersection`

## Ground Truth Sources
- Chapter 83 (Book I, 2nd Ed): Orbit-Set Correspondence

## Mathematical Content

Each generator g determines a "set function" Set(g_n) that maps
a τ-object to a predicate on TauIdx. The five formulas:

- Set(α_n) = { α_k : k ∈_τ n }  (= { α_k : k | n },  divisor set)
- Set(π_n) = { α_k : k = 1 ∨ ∃ j ≤ n, k = nthPrime j }
- Set(γ_n) = { α_k : ∃ e, k = (nthPrime n) ^ e }
- Set(η_n) = { α_k : ∃ j, k = (nthPrime j) ^ n }   (n ≥ 1)
- Set(ω)   = { x : TauObj : x.seed = alpha ∨ (x.seed = omega ∧ x.depth = 0) }

**Key identity**: orbit_set_alpha IS τ-membership (I.D31).
Set(α_n) = {α_k : tau_mem k n}. This is not merely an equivalence
but the SAME relation: the orbit-set for the α-orbit and the
internal membership relation from Part VIII are one concept.

All orbit indices are meaningful only for n ≥ 1 (ℕ⁺).
-/

namespace Tau.Sets

open Tau.Denotation Tau.Coordinates Tau.Kernel Generator

-- ============================================================
-- ORBIT SET: ALPHA [I.D94]
-- ============================================================

/-- [I.D94] Set(α_n): the divisor set = τ-membership.
    α_k ∈ Set(α_n) iff tau_mem k n (iff k | n).

    This IS τ-membership (I.D31) — the orbit-set for α and the
    internal membership relation are the same concept. We define
    orbit_set_alpha in terms of tau_mem to enforce this identity. -/
def orbit_set_alpha (n : TauIdx) (k : TauIdx) : Prop := tau_mem k n

/-- Simp lemma: orbit_set_alpha unfolds to Nat divisibility for proofs. -/
@[simp] theorem orbit_set_alpha_iff_dvd (n k : TauIdx) :
    orbit_set_alpha n k ↔ k ∣ n :=
  tau_mem_iff_dvd k n

noncomputable instance instDecidableOrbitSetAlpha (n k : TauIdx) :
    Decidable (orbit_set_alpha n k) := Classical.dec _

-- ============================================================
-- IDENTITY: ORBIT-SET = τ-MEMBERSHIP
-- ============================================================

/-- The orbit-set for α IS τ-membership — by definition.
    This is a definitional identity, not just a propositional equivalence.
    Part VIII's single-orbit set theory (∈_τ = divisibility) and the
    five-orbit representation theory of Chapter 83 are one theory. -/
theorem orbit_set_alpha_eq_tau_mem (n k : TauIdx) :
    orbit_set_alpha n k ↔ tau_mem k n :=
  Iff.rfl

-- ============================================================
-- ORBIT SET: PI [I.D94]
-- ============================================================

/-- [I.D94] Set(π_n): the set of α-orbit indices belonging to the
    orbit-set of π_n.
    α_k ∈ Set(π_n) iff k = 1 or there exists j ≤ n with k = nthPrime j. -/
def orbit_set_pi (n : TauIdx) (k : TauIdx) : Prop :=
  k = 1 ∨ ∃ j, j ≤ n ∧ k = nthPrime j

noncomputable instance instDecidableOrbitSetPi (n k : TauIdx) :
    Decidable (orbit_set_pi n k) := Classical.dec _

-- ============================================================
-- ORBIT SET: GAMMA [I.D94]
-- ============================================================

/-- [I.D94] Set(γ_n): the set of α-orbit indices belonging to the
    orbit-set of γ_n.
    α_k ∈ Set(γ_n) iff k = p_n ^ e for some e ≥ 0, where p_n = nthPrime n. -/
def orbit_set_gamma (n : TauIdx) (k : TauIdx) : Prop :=
  ∃ e : TauIdx, k = (nthPrime n) ^ e

noncomputable instance instDecidableOrbitSetGamma (n k : TauIdx) :
    Decidable (orbit_set_gamma n k) := Classical.dec _

-- ============================================================
-- ORBIT SET: ETA [I.D94]
-- ============================================================

/-- [I.D94] Set(η_n) for n ≥ 1: the set of α-orbit indices belonging
    to the orbit-set of η_n.
    α_k ∈ Set(η_n) iff k = p_j ^ n for some j. -/
def orbit_set_eta (n : TauIdx) (k : TauIdx) : Prop :=
  ∃ j : TauIdx, k = (nthPrime j) ^ n

noncomputable instance instDecidableOrbitSetEta (n k : TauIdx) :
    Decidable (orbit_set_eta n k) := Classical.dec _

-- ============================================================
-- ORBIT SET: OMEGA [I.D94]
-- ============================================================

/-- [I.D94] Set(ω): the set of τ-objects belonging to the orbit-set of ω.
    x ∈ Set(ω) iff x.seed = alpha or (x.seed = omega and x.depth = 0).

    Note: this predicate acts on TauObj, not TauIdx — ω's orbit-set
    includes itself (the TauObj ⟨omega, 0⟩), which cannot be represented
    as a pure TauIdx predicate. Set(ω) = O_α ∪ {ω} is the universal
    collection — one-point compactification of the counting scaffold. -/
def orbit_set_omega (x : TauObj) : Prop :=
  x.seed = alpha ∨ (x.seed = omega ∧ x.depth = 0)

instance instDecidableOrbitSetOmega (x : TauObj) :
    Decidable (orbit_set_omega x) := by
  unfold orbit_set_omega; exact instDecidableOr

-- ============================================================
-- SELF-CONTAINMENT [I.P41]
-- ============================================================

/-- [I.P41a] Self-containment for α: α_n ∈ Set(α_n) for all n.
    This is tau_mem_refl restated in orbit-set language. -/
theorem self_containment_alpha (n : TauIdx) : orbit_set_alpha n n :=
  tau_mem_refl n

/-- [I.P41b] Self-containment for ω: ⟨omega, 0⟩ ∈ Set(ω).
    Proof: seed = omega and depth = 0. -/
theorem self_containment_omega : orbit_set_omega ⟨omega, 0⟩ :=
  Or.inr ⟨rfl, rfl⟩

-- ============================================================
-- TYPE-LEVEL SEPARATION [I.P41]
-- ============================================================

/-- [I.P41c] Type-level separation for π: π_n (as a TauObj) cannot
    appear in Set(π_n), because orbit_set_pi maps TauIdx → Prop
    (it selects α-orbit indices), while π_n = ⟨pi, n⟩ has seed ≠ alpha.

    We formalize this as: for every n, ⟨pi, n⟩.seed ≠ alpha.
    The orbit-set and the original object live in different
    type-level compartments. -/
theorem not_self_containment_pi (n : TauIdx) :
    (⟨pi, n⟩ : TauObj).seed ≠ alpha := by
  simp

-- ============================================================
-- ORDER BOUND [I.P42]
-- ============================================================

/-- [I.P42] Order bound: if α_k ∈ Set(α_n) and n ≠ 0, then k ≤ n.
    This is tau_mem_le restated in orbit-set language. -/
theorem orbit_set_order_bound (n k : TauIdx)
    (h : orbit_set_alpha n k) (hn : n ≠ 0) : k ≤ n :=
  tau_mem_le h hn

-- ============================================================
-- PRIME ATOM [I.R30]
-- ============================================================

/-- [I.R30] Prime atom theorem: if p is prime, then
    Set(α_p) = {1, p}.
    The only divisors of a prime are 1 and itself. -/
theorem prime_atom (p : TauIdx) (hp : idx_prime p) (k : TauIdx) :
    orbit_set_alpha p k ↔ k = 1 ∨ k = p := by
  simp [orbit_set_alpha_iff_dvd]
  constructor
  · exact hp.2 k
  · intro h
    rcases h with h1 | h2
    · subst h1; exact one_dvd p
    · subst h2; exact dvd_refl k

-- ============================================================
-- UNIT MEMBERSHIP
-- ============================================================

/-- 1 is always in Set(α_n) for every n.
    This is tau_mem_one restated in orbit-set language. -/
theorem orbit_set_alpha_has_one (n : TauIdx) : orbit_set_alpha n 1 :=
  tau_mem_one n

-- ============================================================
-- NO INTERNAL COPY OF O_ALPHA [I.R28]
-- ============================================================

/-- For nonzero n, n+1 is NOT in Set(α_n) (bounded by n). -/
theorem orbit_set_alpha_bounded (n : TauIdx) (hn : n ≠ 0) :
    ¬ orbit_set_alpha n (n + 1) := by
  simp; intro h
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h
  omega

/-- For nonzero n, no single Set(α_n) captures all natural numbers. -/
theorem alpha_orbit_set_not_all (n : TauIdx) (hn : n ≠ 0) :
    ∃ m : TauIdx, ¬ orbit_set_alpha n m :=
  ⟨n + 1, orbit_set_alpha_bounded n hn⟩

/-- [I.R28] ω's orbit-set includes ω itself, so it does not live purely
    in the α-orbit. This is the TauObj-level witness that Set(ω) ≠ O_α. -/
theorem omega_orbit_set_exceeds_alpha :
    orbit_set_omega ⟨omega, 0⟩ ∧ (⟨omega, 0⟩ : TauObj).seed ≠ alpha :=
  ⟨self_containment_omega, by simp⟩

/-- [I.R28] Combined "no internal copy" result: for nonzero n, no Set(α_n)
    captures all of ℕ⁺, and Set(ω) strictly exceeds O_α.

    This expresses the inseparability of ℕ and ω: O_α ≅ ℕ⁺ is NOT
    a valid τ-internal set. The closest is Set(ω) = O_α ∪ {ω}. -/
theorem nat_not_internal_set :
    (∀ n : TauIdx, n ≠ 0 → ∃ m : TauIdx, ¬ orbit_set_alpha n m) ∧
    (orbit_set_omega ⟨omega, 0⟩ ∧ (⟨omega, 0⟩ : TauObj).seed ≠ alpha) :=
  ⟨alpha_orbit_set_not_all, omega_orbit_set_exceeds_alpha⟩

-- ============================================================
-- GAMMA-ETA DUALITY [I.R30]
-- ============================================================

/-- γ-η duality witness: (nthPrime n)^m is in both Set(γ_n) and Set(η_m). -/
theorem gamma_eta_intersection (n m : TauIdx) :
    orbit_set_gamma n ((nthPrime n) ^ m) ∧ orbit_set_eta m ((nthPrime n) ^ m) :=
  ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩

-- ============================================================
-- PI ORBIT-SET MONOTONICITY
-- ============================================================

/-- Set(π_n) ⊆ Set(π_{n+1}): the π orbit-set grows monotonically. -/
theorem orbit_set_pi_monotone (n k : TauIdx) (h : orbit_set_pi n k) :
    orbit_set_pi (n + 1) k := by
  rcases h with rfl | ⟨j, hj, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨j, by simp only [TauIdx] at *; omega, rfl⟩

-- ============================================================
-- GAMMA ALWAYS CONTAINS ONE
-- ============================================================

/-- 1 ∈ Set(γ_n) for all n: take e = 0, so (nthPrime n)^0 = 1. -/
theorem orbit_set_gamma_has_one (n : TauIdx) : orbit_set_gamma n 1 :=
  ⟨0, rfl⟩

-- ============================================================
-- VERIFICATION EXAMPLES
-- ============================================================

-- orbit_set_alpha 6 2: tau_mem 2 6 (= 2 | 6)
example : orbit_set_alpha 6 2 := by simp

-- orbit_set_alpha 12 4: tau_mem 4 12 (= 4 | 12)
example : orbit_set_alpha 12 4 := by simp

-- orbit_set_alpha 12 6: tau_mem 6 12 (= 6 | 12)
example : orbit_set_alpha 12 6 := by simp

-- orbit_set_alpha 1 1: tau_mem 1 1 (= 1 | 1)
example : orbit_set_alpha 1 1 := self_containment_alpha 1

-- orbit_set_pi 2 5: nthPrime 2 = 5
example : orbit_set_pi 2 5 := by
  right; exact ⟨2, by simp only [TauIdx]; omega, by native_decide⟩

-- orbit_set_gamma 0 8: nthPrime 0 = 2, 2^3 = 8
example : orbit_set_gamma 0 8 := ⟨3, by native_decide⟩

-- self-containment for omega
example : orbit_set_omega ⟨omega, 0⟩ := self_containment_omega

-- alpha elements are in Set(ω)
example : orbit_set_omega ⟨alpha, 42⟩ := Or.inl rfl

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Orbit-set membership checks (using decidable instance for orbit_set_omega)
#eval decide (orbit_set_omega ⟨alpha, 5⟩)    -- true
#eval decide (orbit_set_omega ⟨omega, 0⟩)    -- true
#eval decide (orbit_set_omega ⟨pi, 3⟩)       -- false
#eval decide (orbit_set_omega ⟨omega, 1⟩)    -- false

end Tau.Sets

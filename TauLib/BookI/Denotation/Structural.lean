import TauLib.BookI.Polarity.OmegaGerms
import TauLib.BookI.Orbit.Rigidity

/-!
# TauLib.BookI.Denotation.Structural

Structural theorems surfacing the deep difference between τ-Idx and standard Nat.

## The Core Insight

τ-Idx (= Nat as abbreviation) is **not** generic Nat.  It is the *earned* natural
number system discovered as the alpha orbit O_α = {⟨α,0⟩, ⟨α,1⟩, ⟨α,2⟩, ...}.
Structurally it is a *commutative semiring without additive inverses*:

- **No additive zero in the ontological sense**: 0 is the empty product, not a
  destructive absorber.  Additive inverses are only earned at Part IX via
  TauInt formal differences (Boundary/NumberTower.lean).
- **Omega (ω) is a dynamical absorber**: it absorbs ρ (the progression iterator),
  NOT multiplication.  ω is the one-point compactification of N⁺.
- **Almost all properties hold universally**: no "for n ≠ 0" guards needed,
  except for the single locus of multiplicative cancellation.
- **Cauchy-compactness**: the primorial ultrametric on omega-tails induces a
  profinite topology with finite stabilization.

This module makes these facts *explicit* via precise theorems.

## Registry Cross-References

- [I.P06] Arithmetic Laws — earned semiring, no ring
- [I.P07] Well-Ordering — universal, no zero exclusion
- [I.K2]  Omega Fixed Point — dynamical absorber
-/

namespace Tau.Denotation.Structural

open Tau.Kernel Tau.Denotation Tau.Orbit Tau.Coordinates Tau.Polarity Generator

-- ============================================================
-- SECTION 1: EARNED SEMIRING — NOT A RING
-- ============================================================

/-! ## Section 1: Earned Semiring — Not a Ring

τ-Idx forms a commutative semiring (addition, multiplication with identities
0 and 1, distributivity) but *cannot* be extended to a ring within the
earned framework.  The absence of additive inverses is structural, not a deficiency:
ρ generates only positive depth values, so negative depths do not exist in τ. -/

/-- The sum of two τ-Idx values is zero iff both are zero.
    This is the foundational fact: addition on τ-Idx cannot "cancel" to zero. -/
theorem tauIdx_sum_zero_iff (n m : TauIdx) :
    idx_add n m = 0 ↔ n = 0 ∧ m = 0 := by
  simp only [idx_add_eq_nat_add, TauIdx] at *
  constructor
  · intro h; exact ⟨by omega, by omega⟩
  · intro ⟨hn, hm⟩; omega

/-- No positive element has an additive inverse in τ-Idx.
    Ground truth: "Actual infinity (ω) without additive zero" (Book I Reference). -/
theorem tauIdx_no_additive_inverse (n : TauIdx) (hn : n > 0) :
    ¬∃ m : TauIdx, idx_add n m = 0 := by
  intro ⟨m, hm⟩
  simp only [idx_add_eq_nat_add, TauIdx] at *; omega

/-- There exists no negation function on τ-Idx.
    This is the precise statement that τ-Idx is a semiring, not a ring.
    Additive inverses are first earned at Part IX via TauInt formal differences. -/
theorem tauIdx_no_ring_negation :
    ¬∃ neg : TauIdx → TauIdx, ∀ n, idx_add n (neg n) = 0 := by
  intro ⟨neg, h⟩
  have h1 := h 1
  simp only [idx_add_eq_nat_add, TauIdx] at *; omega

-- ============================================================
-- SECTION 2: THE POSITIVE CORE — N⁺ IS CLOSED
-- ============================================================

/-! ## Section 2: The Positive Core — N⁺ is Closed

N⁺ = {n : τ-Idx | n > 0} is closed under all four earned arithmetic operations.
This means the positive elements form an autonomous sub-structure: arithmetic
never "falls" into zero unless it starts there. -/

/-- Addition with a positive argument always yields a positive result. -/
theorem tauIdx_pos_closed_add (n m : TauIdx) (hn : n > 0) :
    idx_add n m > 0 := by
  simp only [idx_add_eq_nat_add, TauIdx] at *; omega

/-- Multiplication of two positive values is positive (no zero divisors in N⁺). -/
theorem tauIdx_pos_closed_mul (n m : TauIdx) (hn : n > 0) (hm : m > 0) :
    idx_mul n m > 0 := by
  rw [idx_mul_eq_nat_mul]; exact Nat.mul_pos hn hm

/-- Exponentiation with positive base is always positive. -/
theorem tauIdx_pos_closed_exp (n : TauIdx) (hn : n > 0) (m : TauIdx) :
    idx_exp n m > 0 := by
  induction m with
  | zero => simp [idx_exp_eq_nat_pow]
  | succ m ih =>
    rw [idx_exp_eq_nat_pow, Nat.pow_succ]
    rw [idx_exp_eq_nat_pow] at ih
    exact Nat.mul_pos ih hn

/-- Every successor is positive: n + 1 > 0 always holds.
    No guard needed — this is universal over τ-Idx. -/
theorem tauIdx_succ_always_pos (n : TauIdx) :
    idx_add n 1 > 0 := by
  simp only [idx_add_eq_nat_add, TauIdx] at *; omega

-- ============================================================
-- SECTION 3: ZERO AS NON-PARTICIPANT
-- ============================================================

/-! ## Section 3: Zero as Non-Participant

Zero in τ-Idx is *vacuous*, not destructive.  It is the unique degenerate
element: it absorbs multiplication and has no prime factorization.  But its
degeneracy is passive — it doesn't participate in the generative dynamics of ρ. -/

/-- Zero is not a prime: it has no prime factorization. -/
theorem tauIdx_zero_not_prime : ¬idx_prime 0 := by
  intro ⟨h, _⟩; simp only [TauIdx] at *; omega

/-- Zero is not a successor: no element of τ-Idx maps to zero under ρ (addition).
    This reflects that the alpha orbit generates only positive depths. -/
theorem tauIdx_zero_not_succ : ¬∃ k : TauIdx, idx_add k 1 = 0 := by
  intro ⟨k, hk⟩; simp only [idx_add_eq_nat_add, TauIdx] at *; omega

/-- **Integral domain property**: the product of two τ-Idx values is zero
    iff at least one factor is zero.  Equivalently: positive × positive = positive.
    There is no "annihilation" except through the vacuous zero. -/
theorem tauIdx_integral_domain (n m : TauIdx) :
    idx_mul n m = 0 ↔ n = 0 ∨ m = 0 := by
  simp only [idx_mul_eq_nat_mul]
  constructor
  · intro h
    -- Forward: n * m = 0 → n = 0 ∨ m = 0 (contrapositive via Nat.mul_pos)
    cases Nat.eq_zero_or_pos n with
    | inl hn => exact Or.inl hn
    | inr hn =>
      cases Nat.eq_zero_or_pos m with
      | inl hm => exact Or.inr hm
      | inr hm =>
        have hpos := Nat.mul_pos hn hm
        rw [h] at hpos
        exact absurd hpos (Nat.lt_irrefl 0)
  · intro h
    cases h with
    | inl h => subst h; simp
    | inr h => subst h; simp

/-- Zero is the unique multiplicative absorber: if a * n = a for all n, then a = 0.
    This rules out any "phantom absorber" in τ-Idx. -/
theorem tauIdx_zero_unique_mul_absorber (a : TauIdx)
    (h : ∀ n, idx_mul a n = a) : a = 0 := by
  have h0 := h 0
  simp [idx_mul_eq_nat_mul] at h0
  exact h0.symm

/-- Zero is divisible by everything (vacuously): every a divides 0.
    This is a restatement of idx_divides_zero for emphasis:
    divisibility into zero is *trivial*, not informative. -/
theorem tauIdx_zero_vacuous_divisor (a : TauIdx) : idx_divides a 0 :=
  idx_divides_zero a

-- ============================================================
-- SECTION 4: UNIVERSAL VS. GUARDED — THE SINGLE FAILURE LOCUS
-- ============================================================

/-! ## Section 4: Universal vs. Guarded — The Single Failure Locus

The dramatic structural fact of τ-Idx: almost every algebraic property holds
*universally* (no "for n ≠ 0" guard).  The single exception is multiplicative
cancellation, which fails exactly at zero.

In ring theory, "for a ≠ 0" qualifications appear everywhere.  In τ-Idx:
- Addition: fully cancellative, universal (Theorem 13)
- Multiplication: cancellative ↔ n > 0 (Theorem 16)
- Divisibility: reflexive, transitive, antisymmetric — all universal
- Well-ordering: universal, no qualification needed -/

/-- Addition is left-cancellative: NO guard needed.
    This is *universal* — it holds for ALL n, including n = 0. -/
theorem tauIdx_add_left_cancel (n a b : TauIdx)
    (h : idx_add n a = idx_add n b) : a = b := by
  simp only [idx_add_eq_nat_add, TauIdx] at *; omega

/-- Addition is right-cancellative: NO guard needed. -/
theorem tauIdx_add_right_cancel (a b n : TauIdx)
    (h : idx_add a n = idx_add b n) : a = b := by
  simp only [idx_add_eq_nat_add, TauIdx] at *; omega

/-- The single failure: multiplicative cancellation breaks at zero.
    0 × 1 = 0 × 2 but 1 ≠ 2. -/
theorem tauIdx_mul_cancel_fails_at_zero :
    idx_mul 0 1 = idx_mul 0 2 := by
  simp [idx_mul_eq_nat_mul]

/-- **The characterization theorem**: multiplicative cancellation holds for n
    if and only if n > 0.  This makes the single zero-sensitive locus maximally explicit.

    Read as: "zero is the unique obstruction to multiplicative cancellation in τ-Idx." -/
theorem tauIdx_mul_cancel_exactly_pos (n : TauIdx) :
    (∀ a b, idx_mul n a = idx_mul n b → a = b) ↔ n > 0 := by
  constructor
  · -- Forward: if n cancels universally, then n > 0
    intro h
    cases Nat.eq_zero_or_pos n with
    | inr hn => exact hn
    | inl hn =>
      -- n = 0: derive contradiction from 0*1 = 0*2 but 1 ≠ 2
      subst hn
      exact absurd (h 1 2 (by simp [idx_mul_eq_nat_mul])) (by decide)
  · -- Backward: if n > 0, then n cancels (from idx_mul_injective)
    intro hn a b hab
    exact idx_mul_injective n hn hab

-- ============================================================
-- SECTION 5: OMEGA AS DYNAMICAL ABSORBER
-- ============================================================

/-! ## Section 5: Omega as Dynamical Absorber

Omega (ω) is the *one-point compactification* of the positive naturals N⁺.
It absorbs the dynamical iterator ρ (fixed point by K2), but it does NOT
absorb algebraic operations (multiplication).  This is the τ-analog of
∞ in N⁺ ∪ {∞}: omega is a topological/dynamical limit, not an algebraic zero.

Key contrast with standard Nat: Nat has 0 as algebraic absorber (0 × n = 0).
τ has ω as dynamical absorber (ρ(ω) = ω).  These are structurally orthogonal. -/

/-- Omega absorbs ρ: the beacon is a fixed point of the progression iterator.
    Restatement of K2 for emphasis in the structural context. -/
theorem omega_rho_absorber (d : Nat) :
    rho ⟨omega, d⟩ = ⟨omega, d⟩ :=
  K2_omega_fixed d

/-- Omega is the UNIQUE fixed seed of ρ: an object x satisfies ρ(x) = x
    if and only if x lives in the omega fiber.
    This characterizes omega as the sole dynamical absorber. -/
theorem omega_unique_fixed_seed (x : TauObj) :
    rho x = x ↔ x.seed = omega := by
  cases x with | mk s d =>
  constructor
  · intro h
    cases s with
    | omega => rfl
    | alpha | pi | gamma | eta => exfalso; simp [rho] at h
  · intro h
    cases s with
    | omega => simp [rho]
    | alpha | pi | gamma | eta => cases h

/-- The alpha orbit has no fixed points of ρ: every TauIdx element
    strictly advances under ρ.  The orbit is genuinely progressive. -/
theorem alpha_orbit_no_fixed_point (n : TauIdx) :
    rho (toAlphaOrbit n) ≠ toAlphaOrbit n := by
  simp [toAlphaOrbit, rho]

/-- The alpha orbit is strictly monotone in depth: higher orbit index
    means strictly greater depth.  There is no "stalling" in the orbit. -/
theorem alpha_orbit_strictly_monotone (n m : TauIdx) (h : n < m) :
    (toAlphaOrbit n).depth < (toAlphaOrbit m).depth := by
  simp [toAlphaOrbit]; exact h

-- ============================================================
-- SECTION 6: FINITE STABILIZATION & COMPACTNESS
-- ============================================================

/-! ## Section 6: Finite Stabilization & Compactness

The primorial ultrametric on omega-tails induces a profinite topology on
the completion space.  The key property is **finite stabilization**: at each
primorial level M_k, two omega-tails either agree or disagree — and agreement
propagates downward through the reduction maps.

This gives τ-Idx its *Cauchy-compact* character: every Compatible sequence
stabilizes at each finite level, making the completion (the space of all
compatible omega-tails) compact.  This is the τ-analog of Ẑ (profinite integers). -/

/-- Helper: diverge_go on identical lists always returns 0. -/
private theorem diverge_go_self (c : List TauIdx) (d i fuel : Nat) :
    diverge_go c c d i fuel = 0 := by
  induction fuel generalizing i with
  | zero => unfold diverge_go; rfl
  | succ n ih =>
    unfold diverge_go
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    split
    · rfl
    · simp [ih]

/-- The ultrametric distance of an omega-tail to itself is zero.
    This is the identity-of-indiscernibles axiom for the earned ultrametric. -/
theorem ultra_dist_self (n d : TauIdx) :
    ultra_dist (mk_omega_tail n d) (mk_omega_tail n d) = 0 := by
  simp only [ultra_dist, divergence_depth, Nat.min_self]
  exact diverge_go_self _ d 0 d

/-- **Finite stabilization**: two numbers congruent modulo M_k produce
    omega-tails that agree at level k.  This is the mechanism behind
    Cauchy-compactness: agreement at level k is determined by a finite check. -/
theorem congruent_tails_agree (n m d k : TauIdx)
    (hk1 : 1 ≤ k) (hkd : k ≤ d)
    (hmod : n % primorial k = m % primorial k) :
    (mk_omega_tail n d).get (k - 1) = (mk_omega_tail m d).get (k - 1) := by
  simp only [OmegaTail.get]
  have hlt : k - 1 < d := by simp only [TauIdx] at *; omega
  rw [mk_omega_tail_getD n d (k - 1) hlt, mk_omega_tail_getD m d (k - 1) hlt]
  have hk : k - 1 + 1 = k := by simp only [TauIdx] at *; omega
  rw [hk]
  exact hmod

-- ============================================================
-- NATIVE_DECIDE VERIFICATIONS
-- ============================================================

-- Section 1: No additive inverse
example : idx_add 3 5 ≠ 0 := by native_decide
example : idx_add 1 0 ≠ 0 := by native_decide

-- Section 2: Positive closure
example : idx_mul 3 7 > 0 := by native_decide
example : idx_exp 2 10 > 0 := by native_decide

-- Section 3: Integral domain
example : idx_mul 3 0 = 0 := by native_decide
example : idx_mul 0 5 = 0 := by native_decide
example : idx_mul 3 5 ≠ 0 := by native_decide

-- Section 4: Cancellation
example : idx_mul 0 1 = idx_mul 0 2 := by native_decide  -- failure at zero
example : idx_mul 0 7 = idx_mul 0 42 := by native_decide  -- failure at zero

-- Section 5: Omega fixed point
example : rho ⟨omega, 0⟩ = ⟨omega, 0⟩ := by native_decide
example : rho ⟨omega, 5⟩ = ⟨omega, 5⟩ := by native_decide
example : rho ⟨alpha, 3⟩ ≠ ⟨alpha, 3⟩ := by native_decide

-- Section 6: Finite stabilization
example : ultra_dist (mk_omega_tail 7 5) (mk_omega_tail 7 5) = 0 := by native_decide
example : ultra_dist (mk_omega_tail 42 5) (mk_omega_tail 42 5) = 0 := by native_decide

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Semiring: no additive inverse exists
#eval (List.range 100).all fun n => idx_add n 1 > 0    -- true: every successor positive

-- Positive core closure
#eval idx_mul 7 13        -- 91 > 0
#eval idx_exp 2 10        -- 1024 > 0

-- Integral domain: product zero iff factor zero
#eval idx_mul 0 42        -- 0
#eval idx_mul 42 0        -- 0
#eval idx_mul 3 7         -- 21 ≠ 0

-- Cancellation failure locus
#eval idx_mul 0 1         -- 0
#eval idx_mul 0 2         -- 0 (same! cancellation fails at 0)
#eval idx_mul 3 4         -- 12
#eval idx_mul 3 5         -- 15 (different! cancellation holds at 3 > 0)

-- Omega as dynamical absorber
#eval rho ⟨omega, 0⟩      -- ⟨omega, 0⟩ (fixed)
#eval rho ⟨alpha, 0⟩      -- ⟨alpha, 1⟩ (advances)

-- Finite stabilization
#eval ultra_dist (mk_omega_tail 7 5) (mk_omega_tail 7 5)     -- 0 (self)
#eval ultra_dist (mk_omega_tail 7 5) (mk_omega_tail 37 5)    -- diverges at some level

end Tau.Denotation.Structural

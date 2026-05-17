import TauLib.BookI.Boundary.ConstructiveReals
import TauLib.BookI.Boundary.SplitComplex
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Boundary.ComplexField

The elliptic complex field as the **cyclotomic-4 adjunction over TauReal**:
`TauComplex := TauReal[X] / (X² + 1)`.

The pair-structure `TauComplex = (re, im)` is the **canonical normal-form
presentation** of that quotient — every element `re + im · X` of the
quotient is uniquely represented by the pair `(re, im)`, and the quotient
relation `X² = -1` is automatically satisfied by the multiplication rule
`(a + bX)(c + dX) = (ac - bd) + (ad + bc)X`.

## Structural framing (Wave Γ₇ Phase 3C reconciliation, 2026-05-14)

τ-canon's **native scalar algebra is split-complex** (`j² = +1`), built
in `BipolarAlgebra.SplitComplex` and `Boundary/SplitComplex.lean`. The
relation `j² = +1` is **kernel-forced via I.T10** — it derives from
the bipolar prime partition demanding idempotents `e_+ · e_- = 0`, and
only `j² = +1` supplies them. This is paper-anchored in 5+ corpus
statements; B-physics (BookIV FCNC) runs entirely on split-complex.

**The orthodox complex relation `i² = -1` is NOT native** to τ-canon's
scalar algebra: Book II ch.08 (lines 88-138) explicitly forbids
`j² = -1`-type algebra at the τ³-interior layer (three independent
kernel-level reasons). The 12 FCNC papers have zero mention of `i² = -1`.

Instead, `i` lives in τ-canon as a **cyclotomic extension** —
specifically, a primitive 4th root of unity adjoined to `TauReal` to
solve the polynomial `X² + 1 = 0`. This is the standard cyclotomic
construction `ℝ[X]/(X²+1) = ℝ[ζ₄]` made τ-native, paper-anchored at
**manuscript ch77** (`ch77-complex-field.tex`).

The structural reading: **`TauComplex` is the elliptic extension of
TauReal beyond the native split-complex algebra**, with `i` as the
canonical cyclotomic-4 root. The pair-structure used in this module
is the normal form of the quotient; the `i² ≈ -1` identity is proved
as the `taucomplex_i_squared` theorem and serves as the defining
relation.

## Rigor label

**[NEW EXTENSION]** (Wave Γ₇ Phase 3C reconciliation): the "elliptic
complex field" appears at I.D85 and is documented at ch77, but the
explicit framing of `i` as a **cyclotomic-4 adjunction** (the
structural-credibility narrative tying it to τ-canon's split-complex
native algebra) is novel to Wave Γ₇. A Book I manuscript paragraph
titled "The Cyclotomic Adjunction" is queued to close this rigor gap
at the paper level.

## Registry Cross-References

- [I.D85] TauComplex — Elliptic complex field over constructive reals
- [I.D86] Elliptic-Hyperbolic Dichotomy — TauComplex (field) vs
  SplitComplex (zero divisors)
- [I.T43] Field Axioms — TauComplex forms a commutative ring (field
  axioms up to equiv)
- [I.T10] (in `BipolarAlgebra.lean`) — `j² = +1` kernel-forced via
  bipolar prime partition (the **native** algebra)
- (Future) `Cyclotomic.lean` — general cyclotomic-tower framework
- Wave Γ₇ Phase 3C reconciliation sprint:
  `atlas/sprints/2026-05-14-tau-canonical-complex-redesign/`

## Ground Truth Sources

- `ch77-complex-field.tex`: Complex field construction as quotient
  `ℂ_τ := ℝ_τ[x] / (x² + 1)`, ring axioms.
- `ch08-foundations-of-the-tau-interior.tex` (lines 88-138): the
  standing reservation against `j² = -1`-type algebra at τ³ interior;
  motivates treating `i` as a cyclotomic extension rather than a
  native primary.
- `BipolarAlgebra.lean` [I.T10]: split-complex paper-forcing.

## Mathematical Content

TauComplex is the standard elliptic complex field built over TauReal:
pairs `(re, im)` with multiplication
`(a + bi)(c + di) = (ac - bd) + (ad + bc)i`.
The defining relation `i² = -1` (elliptic / cyclotomic-4) contrasts
with SplitComplex `j² = +1` (hyperbolic / paper-forced native).
This sign difference has profound consequences:

- **TauComplex** (`i² = -1`, cyclotomic extension): field, no zero
  divisors, algebraically closed (in the algebraic-closure sense).
- **SplitComplex** (`j² = +1`, native): ring with zero divisors,
  sector decomposition, paper-anchored at the kernel level.

All ring axioms are proved up to TauComplex.equiv (componentwise
TauReal.equiv), which reduces pointwise to TauRat.equiv, then to
TauInt.equiv via cross-multiplication, then to Int equality via
`equiv_iff_toInt_eq`.

## Use sites and forward-research targets

* Wave Γ₇ Phase 3C-Part-2+ — `TauComplex.exp_partial` Taylor series
  + Cauchy property (queued).
* Wave Γ₇ Phase 3C-Part-3 — `TauComplex.exp_add` lift from
  `TauReal.exp_add` (the **M3 breakthrough** — sin/cos addition
  formula via exp-addition + i-structure).
* Wave Γ₇ Phase 3C-Part-4 — extract sin/cos addition formulae from
  `cis(α + β) = cis(α) · cis(β)` where `cis(x) := cos(x) + i · sin(x)`.

## Historical note (Wave Γ₇ Phase 3C duplicate cleanup)

Wave Γ₇ Phase 3C Part 1 (commit `529a0af`, 2026-05-14) initially
shipped a `TauRealComplex.lean` module that duplicated this file.
The deep-research red-team sprint
(`atlas/sprints/2026-05-14-tau-canonical-complex-redesign/`)
caught the duplication and identified that:

1. `TauComplex` in this file already provides the full elliptic
   complex field with `i² ≈ -1` proved.
2. The manuscript ch77 already frames the construction as a
   cyclotomic quotient.
3. The orthodox `i` is structurally an extension, not a primary type.

The duplicate `TauRealComplex.lean` was removed, and this docstring
updated to make the cyclotomic-adjunction framing explicit. The
`TauComplex` infrastructure stands as the canonical Lean carrier
for the cyclotomic-4 elliptic complex field.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- [I.D85] TauComplex: ELLIPTIC COMPLEX FIELD
-- ============================================================

/-- [I.D85] TauComplex: the elliptic complex field TauReal[i]/(i² + 1).
    A pair (re, im) represents re + im * i. -/
structure TauComplex where
  /-- Real part. -/
  re : TauReal
  /-- Imaginary part. -/
  im : TauReal

-- ============================================================
-- EQUIVALENCE: COMPONENTWISE TauReal.equiv
-- ============================================================

/-- Two TauComplex values are equivalent if their real and imaginary
    parts are equivalent as TauReals. -/
def TauComplex.equiv (a b : TauComplex) : Prop :=
  TauReal.equiv a.re b.re ∧ TauReal.equiv a.im b.im

/-- TauComplex equivalence is reflexive. -/
theorem TauComplex.equiv_refl (a : TauComplex) : TauComplex.equiv a a :=
  ⟨TauReal.equiv_refl a.re, TauReal.equiv_refl a.im⟩

/-- TauComplex equivalence is symmetric. -/
theorem TauComplex.equiv_symm {a b : TauComplex} (h : TauComplex.equiv a b) :
    TauComplex.equiv b a :=
  ⟨TauReal.equiv_symm h.1, TauReal.equiv_symm h.2⟩

-- ============================================================
-- BASIC OPERATIONS
-- ============================================================

/-- Complex zero: (0, 0). -/
def TauComplex.zero : TauComplex := ⟨TauReal.zero, TauReal.zero⟩

/-- Complex one: (1, 0). -/
def TauComplex.one : TauComplex := ⟨TauReal.one, TauReal.zero⟩

/-- The imaginary unit: i = (0, 1). -/
def TauComplex.i_unit : TauComplex := ⟨TauReal.zero, TauReal.one⟩

/-- Complex addition: (a + bi) + (c + di) = (a+c) + (b+d)i. -/
def TauComplex.add (a b : TauComplex) : TauComplex :=
  ⟨TauReal.add a.re b.re, TauReal.add a.im b.im⟩

/-- Complex multiplication: (a + bi)(c + di) = (ac - bd) + (ad + bc)i.
    Note: subtraction is TauReal.sub = TauReal.add ∘ TauReal.negate. -/
def TauComplex.mul (a b : TauComplex) : TauComplex :=
  ⟨TauReal.sub (TauReal.mul a.re b.re) (TauReal.mul a.im b.im),
   TauReal.add (TauReal.mul a.re b.im) (TauReal.mul a.im b.re)⟩

/-- Complex negation: -(a + bi) = (-a) + (-b)i. -/
def TauComplex.negate (a : TauComplex) : TauComplex :=
  ⟨TauReal.negate a.re, TauReal.negate a.im⟩

/-- Complex conjugation: conj(a + bi) = a + (-b)i. -/
def TauComplex.conj (a : TauComplex) : TauComplex :=
  ⟨a.re, TauReal.negate a.im⟩

-- ============================================================
-- i² = -1 (THE DEFINING RELATION)
-- ============================================================

/-- The defining relation of the complex field: i² = -1.
    mul(0,1)(0,1) = (0*0 - 1*1, 0*1 + 1*0) = (-1, 0) = negate(1, 0). -/
theorem taucomplex_i_squared :
    TauComplex.equiv (TauComplex.mul TauComplex.i_unit TauComplex.i_unit)
                     (TauComplex.negate TauComplex.one) := by
  constructor
  · -- Real part: sub(mul(0,0), mul(1,1)) ≡ negate(1) i.e. 0*0 - 1*1 ≡ -1
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauComplex.i_unit, TauComplex.negate, TauComplex.one,
               TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate, TauRat.zero, TauRat.one]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    push_cast; try ring
  · -- Imaginary part: add(mul(0,1), mul(1,0)) ≡ negate(0) i.e. 0*1 + 1*0 ≡ 0
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauComplex.i_unit, TauComplex.negate, TauComplex.one,
               TauReal.add, TauReal.mul, TauReal.negate, TauReal.zero, TauReal.one]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.negate, TauRat.zero, TauRat.one]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    push_cast; try ring

-- ============================================================
-- [I.T43] RING AXIOMS (UP TO equiv)
-- ============================================================

/-- Addition is commutative. -/
theorem taucomplex_add_comm (a b : TauComplex) :
    TauComplex.equiv (TauComplex.add a b) (TauComplex.add b a) :=
  ⟨taureal_add_comm a.re b.re, taureal_add_comm a.im b.im⟩

/-- Addition is associative. -/
theorem taucomplex_add_assoc (a b c : TauComplex) :
    TauComplex.equiv ((TauComplex.add (TauComplex.add a b) c))
                     (TauComplex.add a (TauComplex.add b c)) :=
  ⟨taureal_add_assoc a.re b.re c.re, taureal_add_assoc a.im b.im c.im⟩

/-- Zero is a right identity for addition. -/
theorem taucomplex_add_zero (a : TauComplex) :
    TauComplex.equiv (TauComplex.add a TauComplex.zero) a :=
  ⟨taureal_add_zero a.re, taureal_add_zero a.im⟩

/-- Negation is a right inverse for addition. -/
theorem taucomplex_add_negate (a : TauComplex) :
    TauComplex.equiv (TauComplex.add a (TauComplex.negate a)) TauComplex.zero :=
  ⟨taureal_add_negate a.re, taureal_add_negate a.im⟩

/-- Multiplication is commutative.
    Re: ac - bd = ca - db. Im: ad + bc = cb + da. -/
theorem taucomplex_mul_comm (a b : TauComplex) :
    TauComplex.equiv (TauComplex.mul a b) (TauComplex.mul b a) := by
  constructor
  · -- Real part: sub(mul(a.re, b.re), mul(a.im, b.im)) ≡ sub(mul(b.re, a.re), mul(b.im, a.im))
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate]
    simp only [TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat]
    push_cast; try ring
  · -- Imaginary part: add(mul(a.re, b.im), mul(a.im, b.re)) ≡ add(mul(b.re, a.im), mul(b.im, a.re))
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauReal.add, TauReal.mul]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_fromNat]
    push_cast; try ring

/-- Multiplication is associative.
    (ab)c = a(bc) for complex multiplication. -/
theorem taucomplex_mul_assoc (a b c : TauComplex) :
    TauComplex.equiv (TauComplex.mul (TauComplex.mul a b) c)
                     (TauComplex.mul a (TauComplex.mul b c)) := by
  constructor
  · -- Real part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate]
    simp only [TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat]
    push_cast; try ring
  · -- Imaginary part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate]
    simp only [TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat]
    push_cast; try ring

/-- One is a right identity for multiplication: z * 1 = z. -/
theorem taucomplex_mul_one (a : TauComplex) :
    TauComplex.equiv (TauComplex.mul a TauComplex.one) a := by
  constructor
  · -- Real part: a.re * 1 - a.im * 0 ≡ a.re
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauComplex.one, TauReal.sub, TauReal.add, TauReal.mul,
               TauReal.negate, TauReal.one, TauReal.zero]
    simp only [TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate,
               TauRat.one, TauRat.zero]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one]
    push_cast; try ring
  · -- Imaginary part: a.re * 0 + a.im * 1 ≡ a.im
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauComplex.one, TauReal.add, TauReal.mul,
               TauReal.one, TauReal.zero]
    simp only [TauRat.equiv, TauRat.add, TauRat.mul, TauRat.one, TauRat.zero]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_fromNat, toInt_zero, toInt_one]
    push_cast; try ring

/-- Left distributivity: a * (b + c) = a*b + a*c. -/
theorem taucomplex_left_distrib (a b c : TauComplex) :
    TauComplex.equiv (TauComplex.mul a (TauComplex.add b c))
                     (TauComplex.add (TauComplex.mul a b) (TauComplex.mul a c)) := by
  constructor
  · -- Real part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauComplex.add, TauReal.sub, TauReal.add, TauReal.mul,
               TauReal.negate]
    simp only [TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat]
    push_cast; try ring
  · -- Imaginary part
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.mul, TauComplex.add, TauReal.sub, TauReal.add, TauReal.mul,
               TauReal.negate]
    simp only [TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat]
    push_cast; try ring

/-- Full TauComplex ring axiom collection. -/
theorem taucomplex_ring_axioms :
    (∀ (a b : TauComplex), TauComplex.equiv (a.add b) (b.add a)) ∧
    (∀ (a b c : TauComplex), TauComplex.equiv ((a.add b).add c) (a.add (b.add c))) ∧
    (∀ (a : TauComplex), TauComplex.equiv (a.add TauComplex.zero) a) ∧
    (∀ (a : TauComplex), TauComplex.equiv (a.add a.negate) TauComplex.zero) ∧
    (∀ (a b : TauComplex), TauComplex.equiv (a.mul b) (b.mul a)) ∧
    (∀ (a b c : TauComplex), TauComplex.equiv ((a.mul b).mul c) (a.mul (b.mul c))) ∧
    (∀ (a : TauComplex), TauComplex.equiv (a.mul TauComplex.one) a) ∧
    (∀ (a b c : TauComplex), TauComplex.equiv (a.mul (b.add c)) ((a.mul b).add (a.mul c))) :=
  ⟨taucomplex_add_comm, taucomplex_add_assoc, taucomplex_add_zero, taucomplex_add_negate,
   taucomplex_mul_comm, taucomplex_mul_assoc, taucomplex_mul_one,
   taucomplex_left_distrib⟩

-- ============================================================
-- [I.D86] ELLIPTIC-HYPERBOLIC DICHOTOMY
-- ============================================================

/-- [I.D86] The elliptic-hyperbolic dichotomy:
    - TauComplex has i² = -1 (elliptic sign), yielding a field with no zero divisors.
    - SplitComplex has j² = +1 (hyperbolic sign), yielding a ring WITH zero divisors.

    We witness the dichotomy by showing:
    1. i² = -1 in TauComplex (taucomplex_i_squared)
    2. j² = +1 in SplitComplex (sc_j_squared, proved below)
    3. SplitComplex has zero divisors (zero_divisor_witness_b from SplitComplex.lean) -/
theorem sc_j_squared :
    SplitComplex.mul ⟨0, 1⟩ ⟨0, 1⟩ = SplitComplex.one := by
  simp [SplitComplex.mul, SplitComplex.one]

/-- The dichotomy: i² = -1 AND j² = +1 AND SplitComplex has zero divisors. -/
theorem elliptic_hyperbolic_dichotomy :
    -- i² = -1 (elliptic)
    TauComplex.equiv (TauComplex.mul TauComplex.i_unit TauComplex.i_unit)
                     (TauComplex.negate TauComplex.one) ∧
    -- j² = +1 (hyperbolic)
    SplitComplex.mul ⟨0, 1⟩ ⟨0, 1⟩ = SplitComplex.one ∧
    -- SplitComplex has zero divisors: (1+j)(1-j) = 0
    SplitComplex.mul ⟨1, 1⟩ ⟨1, -1⟩ = SplitComplex.zero :=
  ⟨taucomplex_i_squared, sc_j_squared, by simp [SplitComplex.mul, SplitComplex.zero]⟩

-- ============================================================
-- EMBEDDING: TauReal → TauComplex
-- ============================================================

/-- Embed a TauReal into TauComplex as the real part with zero imaginary part. -/
def TauComplex.fromTauReal (r : TauReal) : TauComplex :=
  ⟨r, TauReal.zero⟩

/-- The embedding preserves addition (up to equiv). -/
theorem fromTauReal_add (a b : TauReal) :
    TauComplex.equiv (TauComplex.fromTauReal (TauReal.add a b))
                     (TauComplex.add (TauComplex.fromTauReal a) (TauComplex.fromTauReal b)) :=
  ⟨TauReal.equiv_refl _, taureal_add_zero TauReal.zero⟩

-- ============================================================
-- CONJUGATION PROPERTIES
-- ============================================================

/-- Conjugation is an involution: conj(conj(z)) ≡ z. -/
theorem taucomplex_conj_involution (a : TauComplex) :
    TauComplex.equiv (TauComplex.conj (TauComplex.conj a)) a := by
  constructor
  · exact TauReal.equiv_refl a.re
  · -- negate(negate(a.im)) ≡ a.im
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.conj, TauReal.negate]
    simp only [TauRat.equiv, TauRat.negate]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_negate, toInt_mul, toInt_fromNat]
    push_cast; try ring

/-- Conjugation distributes over addition: conj(a + b) ≡ conj(a) + conj(b). -/
theorem taucomplex_conj_add (a b : TauComplex) :
    TauComplex.equiv (TauComplex.conj (TauComplex.add a b))
                     (TauComplex.add (TauComplex.conj a) (TauComplex.conj b)) := by
  constructor
  · exact TauReal.equiv_refl _
  · -- negate(add(a.im, b.im)) ≡ add(negate(a.im), negate(b.im))
    apply TauReal.equiv_of_pointwise
    intro n
    simp only [TauComplex.conj, TauComplex.add, TauReal.negate, TauReal.add]
    simp only [TauRat.equiv, TauRat.negate, TauRat.add]
    rw [equiv_iff_toInt_eq]
    simp only [toInt_add, toInt_negate, toInt_mul, toInt_fromNat]
    push_cast; try ring

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Type checks
#check TauComplex
#check TauComplex.equiv
#check TauComplex.i_unit
#check TauComplex.mul
#check TauComplex.conj

-- Theorem checks
#check taucomplex_i_squared
#check taucomplex_add_comm
#check taucomplex_add_assoc
#check taucomplex_add_zero
#check taucomplex_add_negate
#check taucomplex_mul_comm
#check taucomplex_mul_assoc
#check taucomplex_mul_one
#check taucomplex_left_distrib
#check taucomplex_ring_axioms
#check elliptic_hyperbolic_dichotomy
#check taucomplex_conj_involution
#check taucomplex_conj_add

end Tau.Boundary

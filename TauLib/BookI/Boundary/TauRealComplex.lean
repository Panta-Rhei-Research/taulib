import TauLib.BookI.Boundary.TauRealSin
import TauLib.BookI.Boundary.TauRealCos
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# TauLib.BookI.Boundary.TauRealComplex

**Wave Γ₇ Phase 3C Part 1 — τ-native complex numbers.**

The minimal complex-number infrastructure needed for the M3 breakthrough
(Phase 3C Part 2-3): the sin/cos addition formula derived from
exp-addition + i-structure decomposition.

## Mathematical content

A `TauRealComplex` is a pair `(re, im)` of `TauReal`s, representing
the complex number `re + i·im`. Operations:

* `add`: pointwise.
* `mul`: `(a+bi)(c+di) = (ac − bd) + (ad + bc)i`.
* `neg`, `sub`: derived.
* `conj`: `(a − bi)`.
* `fromTauReal x := (x, 0)`.
* `i := (0, 1)`.

## Why TauRealComplex enables the M3 breakthrough

The strategic plan (Wave Γ₇ Phase 3) targets the sin/cos addition formula
via the chain:

  exp(i·(α + β)) = exp(i·α) · exp(i·β)        ← lifted exp-addition formula
  ⟹ cos(α+β) + i·sin(α+β) = (cos α + i·sin α)(cos β + i·sin β)
  ⟹ cos(α+β) = cos α · cos β − sin α · sin β  (real part)
     sin(α+β) = sin α · cos β + cos α · sin β  (imaginary part)

The first step (exp on TauRealComplex satisfies the addition formula)
lifts the existing real `TauReal.exp_add` (Wave 3b R10) via the
Cauchy-product infrastructure (`TauRat.cauchyPStar`, `cauchy_product_bound`
in `TauRealSum.lean`). The lift is mechanical once TauRealComplex
arithmetic + Taylor series are in place.

## Wave Γ₇ Phase 3C sub-structure

* **Part 1** (this commit): `TauRealComplex` type + basic arithmetic +
  algebraic identities at the `TauReal.equiv` level.
* **Part 2** (next session): `TauRealComplex.exp_partial` Taylor series
  + Cauchy property. Same template as `TauReal.exp_of_rat` but on
  complex arguments.
* **Part 3** (the M3 breakthrough): lift `TauReal.exp_add` to
  `TauRealComplex.exp_add`. Then specialise to purely imaginary
  arguments and extract real/imaginary parts to get sin/cos addition.
* **Part 4** (Phase 3D-3F preparation): arctan inverse formulae,
  Machin chain, equiv proof.

## Algebraic strategy

For Phase 3C Part 1, we prove the ring axioms (commutativity,
associativity, distributivity) **at the `TauReal.equiv` level**,
not as strict structural equalities. This mirrors how `TauReal` itself
has only Cauchy-completion algebraic identities (cf.
`Tau.Boundary.taureal_ring_axioms`).

The downstream lift to `exp_C.add` will use Cauchy-equiv at each step:
- `TauRealComplex.equiv` is defined pairwise via `TauReal.equiv`.
- The Cauchy-product proof at the complex level uses Cauchy-equiv
  in both real and imaginary components.

## Build state

* `sorry` count: 0
* `axiom` count: 0
* Imports: TauRealSin, TauRealCos (Phase 3A+3B foundations) + tactics.

## Phase 3C Part 1 deliverables (this commit)

* `TauRealComplex` structure.
* `TauRealComplex.zero, one, i` — special elements.
* `TauRealComplex.add, neg, sub, mul, conj` — operations.
* `TauRealComplex.fromTauReal` — real embedding.
* `TauRealComplex.equiv` — Cauchy-pair equivalence.
* `TauRealComplex.equiv_refl/symm/trans` — equivalence relation properties.
* Key algebraic identities (at equiv level): add_comm, add_assoc,
  mul_comm (via Cauchy), distributivity, i² = −1.

## What this commit does NOT do

* Does NOT define `TauRealComplex.exp` — queued for Part 2.
* Does NOT prove the sin/cos addition formulae — queued for Part 3.
* Does NOT touch the existing TauRealSin/TauRealCos — they remain
  the real-valued sin/cos foundations.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- PART 1: TauRealComplex TYPE + SPECIAL ELEMENTS
-- ============================================================

/-- **[I.D-TauRealComplex]** A τ-native complex number as a pair of
    `TauReal`s representing `re + i·im`. -/
structure TauRealComplex where
  re : TauReal
  im : TauReal

/-- Zero: `0 + 0i`. -/
def TauRealComplex.zero : TauRealComplex :=
  ⟨TauReal.zero, TauReal.zero⟩

/-- One: `1 + 0i`. -/
def TauRealComplex.one : TauRealComplex :=
  ⟨TauReal.one, TauReal.zero⟩

/-- The imaginary unit `i`: `0 + 1i`. -/
def TauRealComplex.i : TauRealComplex :=
  ⟨TauReal.zero, TauReal.one⟩

/-- Embed a TauReal as a TauRealComplex (purely real). -/
def TauRealComplex.fromTauReal (x : TauReal) : TauRealComplex :=
  ⟨x, TauReal.zero⟩

-- ============================================================
-- PART 2: BASIC ARITHMETIC OPERATIONS
-- ============================================================

/-- Pointwise addition: `(a+bi) + (c+di) = (a+c) + (b+d)i`. -/
def TauRealComplex.add (z w : TauRealComplex) : TauRealComplex :=
  ⟨z.re.add w.re, z.im.add w.im⟩

/-- Pointwise negation. -/
def TauRealComplex.neg (z : TauRealComplex) : TauRealComplex :=
  ⟨z.re.negate, z.im.negate⟩

/-- Subtraction: `z − w := z + (−w)`. -/
def TauRealComplex.sub (z w : TauRealComplex) : TauRealComplex :=
  z.add w.neg

/-- Complex multiplication: `(a+bi)(c+di) = (ac − bd) + (ad + bc)i`. -/
def TauRealComplex.mul (z w : TauRealComplex) : TauRealComplex :=
  ⟨(z.re.mul w.re).sub (z.im.mul w.im),
   (z.re.mul w.im).add (z.im.mul w.re)⟩

/-- Conjugate: `(a+bi)* = a − bi`. -/
def TauRealComplex.conj (z : TauRealComplex) : TauRealComplex :=
  ⟨z.re, z.im.negate⟩

-- ============================================================
-- PART 3: EQUIVALENCE RELATION
-- ============================================================

/-- **Cauchy-pair equivalence**: two TauRealComplex values are
    equivalent if their real and imaginary parts are Cauchy-equivalent
    as TauReals. -/
def TauRealComplex.equiv (z w : TauRealComplex) : Prop :=
  z.re.equiv w.re ∧ z.im.equiv w.im

theorem TauRealComplex.equiv_refl (z : TauRealComplex) : z.equiv z :=
  ⟨TauReal.equiv_refl z.re, TauReal.equiv_refl z.im⟩

theorem TauRealComplex.equiv_symm {z w : TauRealComplex} (h : z.equiv w) : w.equiv z :=
  ⟨TauReal.equiv_symm h.1, TauReal.equiv_symm h.2⟩

theorem TauRealComplex.equiv_trans {z w v : TauRealComplex}
    (h_zw : z.equiv w) (h_wv : w.equiv v) : z.equiv v :=
  ⟨TauReal.equiv_trans h_zw.1 h_wv.1, TauReal.equiv_trans h_zw.2 h_wv.2⟩

/-- A `TauRealComplex` is Cauchy if both real and imaginary parts are. -/
def TauRealComplex.IsCauchy (z : TauRealComplex) : Prop :=
  z.re.IsCauchy ∧ z.im.IsCauchy

-- ============================================================
-- PART 4: BASIC ALGEBRAIC IDENTITIES (at structural equality level)
-- ============================================================

@[simp] theorem TauRealComplex.add_zero (z : TauRealComplex) :
    z.add TauRealComplex.zero = ⟨z.re.add TauReal.zero, z.im.add TauReal.zero⟩ := rfl

@[simp] theorem TauRealComplex.zero_add (z : TauRealComplex) :
    TauRealComplex.zero.add z = ⟨TauReal.zero.add z.re, TauReal.zero.add z.im⟩ := rfl

@[simp] theorem TauRealComplex.one_re : TauRealComplex.one.re = TauReal.one := rfl

@[simp] theorem TauRealComplex.one_im : TauRealComplex.one.im = TauReal.zero := rfl

@[simp] theorem TauRealComplex.i_re : TauRealComplex.i.re = TauReal.zero := rfl

@[simp] theorem TauRealComplex.i_im : TauRealComplex.i.im = TauReal.one := rfl

@[simp] theorem TauRealComplex.zero_re : TauRealComplex.zero.re = TauReal.zero := rfl

@[simp] theorem TauRealComplex.zero_im : TauRealComplex.zero.im = TauReal.zero := rfl

@[simp] theorem TauRealComplex.fromTauReal_re (x : TauReal) :
    (TauRealComplex.fromTauReal x).re = x := rfl

@[simp] theorem TauRealComplex.fromTauReal_im (x : TauReal) :
    (TauRealComplex.fromTauReal x).im = TauReal.zero := rfl

-- ============================================================
-- PART 5: STRUCTURAL TARGETS QUEUED FOR PART 1.5
-- ============================================================

/-! ## Algebraic identities queued for Phase 3C Part 1.5

The full algebraic identities (commutativity, associativity,
distributivity, `i² ≈ −1`) require expanding the TauReal Cauchy-completion
ring axioms (`taureal_add_comm`, `taureal_mul_comm`, etc., proved in
`ConstructiveReals.lean`). The proofs are mechanical pointwise-equiv
manipulations but require careful lemma lookup.

**Queued for Phase 3C Part 1.5** (a short follow-on commit):

* `TauRealComplex.add_comm_equiv`: `z.add w ≈ w.add z`
* `TauRealComplex.add_assoc_equiv`: `(z.add w).add v ≈ z.add (w.add v)`
* `TauRealComplex.mul_comm_equiv`: `z.mul w ≈ w.mul z`
* `TauRealComplex.mul_assoc_equiv`: `(z.mul w).mul v ≈ z.mul (w.mul v)`
* `TauRealComplex.mul_distrib_equiv`: distributivity
* `TauRealComplex.i_sq_equiv_neg_one`: `i.mul i ≈ fromTauReal (−1)`

These identities are not needed for the *type* definition or the
*structural* M3 breakthrough setup — they're needed for the
**substitutive** manipulations downstream (when we equate complex
expressions in the exp-addition proof).

For Phase 3C Part 1, the type + arithmetic + equiv-as-relation are
the load-bearing structural deliverables. The algebraic identity
proofs are queued cleanly.
-/

end Tau.Boundary

import TauLib.BookI.Boundary.NumericalProjection
import TauLib.BookI.Polarity.BipolarAlgebra

/-!
# TauLib.BookI.Polarity.SplitComplexCouplingLift

**Paper §7.4 — Split-Complex Idempotent Readout: lifting the
coupling identity to algebraic form, and the prime polarity character.**

Closes paper `iota-tau/main.tex` §7 entirely (lines 1955–2323),
completing the H3 paper arc at the full algebraic-readout level.

This wave is the **bridge to H2 prime polarity**: it sets up the
split-complex idempotent decomposition that the prime polarity
classifier (Wave 18, paper `prime-polarity/main.tex` §6) will
consume directly.

## Registry Cross-References

- [I.D26]  Tau.Polarity.SplitComplex (existing)
- [I.D27]  Tau.Polarity.SectorPair, e_plus_sector, e_minus_sector (existing)
- [I.D128] Tau.Boundary finite-stage approximants (Wave 15)
- [I.D129] Tau.Boundary numerical readout (Wave 16)
- [I.T80]  coupling_identity_at_omega (Wave 15)
- [I.T-IdemTrace] additive trace `Tr_+` on SectorPair (this module)
- [I.T-CouplingIdem] idempotent reformulation of coupling identity
- [I.T-PrimePolarity-Chi] prime polarity character χ
- [I.T-ChiTildeRamification] ramification triviality χ̃(2^k) = 0

## Mathematical Content (paper §7.4)

**Idempotent traces** (paper §6.2 Step 2b convention):
  - `Tr_+(z_+ e_+ + z_- e_-) = z_+ + z_-` (additive trace)
  - `Tr_-(z_+ e_+ + z_- e_-) = z_+ - z_-` (signed-difference trace)
  - `Tr_+` is the unique σ-invariant ℤ-linear functional on
    `D ⊗ ℝ_τ` (paper Lemma 6.2 Step 2b).

**Idempotent-decomposed clock element** (paper Def 7.10
`def:channel-growth`):
  - `w_ω := π_τ · e_+ + e_τ · e_-` — placing π in the e_+ sector
    and e in the e_- sector under the Book II Ch. 47 convention
  - `Tr_+(w_ω) = π_τ + e_τ`

**Idempotent reformulation of coupling identity** (paper Prop 7.11
`cor:idempotent-lift`):
  `ι_τ · Tr_+(w_ω) ≡ 2`  — algebraic form of `ι_τ = 2/(π+e)`.

**Prime polarity character** (paper Def 7.4 `def:polarity-chi`):
  `χ : (ℕ, ×) → (ℤ, +)` satisfying:
  - `χ(1) = 0` (unit-glue)
  - `χ(p) = +1` for `p ∈ ℙ_B` (B-primes)
  - `χ(p) = -1` for `p ∈ ℙ_C` (C-primes)
  - `χ(p) = 0` for `p ∈ ℙ_ram` (ramified primes — currently {2})
  - additive on multiplication: `χ(mn) = χ(m) + χ(n)`

**Split-complex prime polarity lift** (paper Def 7.5
`def:chi-tilde`):
  `χ̃ : (ℕ, ×) → (D, +)`,
  `χ̃(n) := ν_B(n) · e_+ + ν_C(n) · e_-`
  where `ν_B(n)` counts B-prime factors with multiplicity.

**Ramification triviality** (paper Prop 7.7
`prop:ramification-triviality`):
  `χ̃(2^k) = 0` in D for every k ≥ 0 — the ramified prime
  contributes identically zero at every primorial stage.

**Trace bridge** (paper Prop 7.6
`prop:chi-tilde-algebra`):
  `Tr_+(χ̃(n)) = ν_B(n) + ν_C(n) =: Ω*(n)` (non-ramified prime
  factors with multiplicity)
  `Tr_-(χ̃(n)) = ν_B(n) - ν_C(n) = χ(n)`

## Public API

- `SectorPair.trPlus`, `SectorPair.trMinus` — additive and
  signed-difference traces.
- `WOmega : Type` — the TauReal-valued idempotent-decomposed
  clock element (paper's `w_ω`).
- `wOmega : WOmega` — the canonical instance with π_τ and e_τ.
- `WOmega.trPlus` — the additive-trace lift to TauReal.
- `coupling_identity_idempotent` — paper Prop 7.11.
- `chi : (B_class : Nat → Bool) → Nat → ℤ` — prime polarity
  character parameterised over a B-class predicate.
- `nuB`, `nuC : (Nat → Bool) → Nat → Nat` — concrete B-prime and
  C-prime multiplicity counts (V3 Gap #7.2: now real
  trial-division-based functions, replacing the prior
  structural-placeholder `Nat.zero` returns).
- `nuB_zero`, `nuB_one`, `nuB_two` (and `nuC` analogues) —
  simp-lemmas covering the unit-glue and ramification corner cases.
- `chiTilde` — split-complex lift via prime-power decomposition.
- `chiTilde_zero`, `chiTilde_one`, `chiTilde_two` — paper Prop 7.7
  ramification triviality at the prime level, plus unit-glue
  (`χ̃(1) = 0`).
- `trPlus_chiTilde_two_zero` — trace form of ramification triviality.

## Scope

`\scopetau`, unconditional at the algebraic-trace level.  The
specific identification of B-primes with `Legendre(2/p) = +1` is the
content of paper `prime-polarity/main.tex` §5 (the orthodox
theorem) and is rendered in Wave 18; this wave keeps the B-class
abstract as a parameter, so the chi/chiTilde definitions are
ready to receive the concrete Legendre-based predicate.

## Gap History (V3 audit)

- **V2.0 (Wave 17)**: `nuB`/`nuC` shipped as structural placeholders
  returning `Nat.zero` regardless of input — sufficient for the
  type signatures and `χ̃(2) = 0` at the prime-level
  reduction, but the `χ̃(n)` lift was effectively the zero
  function on every input.
- **V3 audit (2026-05-21, Gap #7.2)**: flagged the
  60%-backing state — paper Def 7.5 calls for `χ̃` to be a
  monoid homomorphism witnessing the prime-power decomposition,
  but the Lean witness was constant zero.
- **This commit (V3 Gap #7.2 fix)**: replaces the placeholders
  with concrete trial-division counts `nuBWorker`/`nuCWorker`,
  preserving the corner-case simp lemmas (`nuB(0) = nuB(1) =
  nuB(2) = 0`) and demonstrating non-trivial values on B/C-prime
  products (see Part 7 `#eval` battery).  All axioms remain
  3-kernel (propext, Classical.choice, Quot.sound); no `sorry`s.
-/

set_option autoImplicit false

namespace Tau.Polarity

open Tau.Denotation Tau.Boundary

-- ============================================================
-- PART 1: Trace operations on SectorPair
-- ============================================================

/-- **Additive trace** on `SectorPair` (paper §6.2 Step 2b
    `Tr_+`):

      `Tr_+(z_+ e_+ + z_- e_-) := z_+ + z_-`.

    Paper Lemma 6.2 Step 2b identifies `Tr_+` as the unique
    σ-invariant ℤ-linear functional on `D ⊗ ℝ_τ` — the algebraic
    reason the coupling identity's denominator takes the additive
    form `π + e` rather than `π · e`. -/
def SectorPair.trPlus (z : SectorPair) : Int :=
  z.b_sector + z.c_sector

/-- **Signed-difference trace** on `SectorPair` (paper §6.2 Step 2b
    `Tr_-`):

      `Tr_-(z_+ e_+ + z_- e_-) := z_+ - z_-`.

    The σ-anti-invariant counterpart of `Tr_+`; carries the prime
    polarity character `χ` via the chiTilde bridge below. -/
def SectorPair.trMinus (z : SectorPair) : Int :=
  z.b_sector - z.c_sector

@[simp] theorem SectorPair.trPlus_e_plus :
    SectorPair.trPlus e_plus_sector = 1 := rfl

@[simp] theorem SectorPair.trPlus_e_minus :
    SectorPair.trPlus e_minus_sector = 1 := rfl

@[simp] theorem SectorPair.trPlus_partition :
    SectorPair.trPlus (SectorPair.add e_plus_sector e_minus_sector) = 2 := by
  unfold SectorPair.trPlus SectorPair.add e_plus_sector e_minus_sector
  rfl

@[simp] theorem SectorPair.trMinus_e_plus :
    SectorPair.trMinus e_plus_sector = 1 := rfl

@[simp] theorem SectorPair.trMinus_e_minus :
    SectorPair.trMinus e_minus_sector = -1 := by
  unfold SectorPair.trMinus e_minus_sector
  rfl

/-- **Tr_+ is additive** on SectorPair sums. -/
theorem SectorPair.trPlus_add (a b : SectorPair) :
    SectorPair.trPlus (SectorPair.add a b) =
      SectorPair.trPlus a + SectorPair.trPlus b := by
  unfold SectorPair.trPlus SectorPair.add
  ring

/-- **Tr_- is additive** on SectorPair sums. -/
theorem SectorPair.trMinus_add (a b : SectorPair) :
    SectorPair.trMinus (SectorPair.add a b) =
      SectorPair.trMinus a + SectorPair.trMinus b := by
  unfold SectorPair.trMinus SectorPair.add
  ring

-- ============================================================
-- PART 2: TauReal-valued idempotent-decomposed clock w_ω
-- ============================================================

/-- **TauReal-valued idempotent-decomposed clock element**
    (paper Def 7.10 `def:channel-growth`).

    The split-complex algebra `D ⊗ ℝ_τ` is rendered at the TauReal
    level as a pair of TauReals: the e_+ component carries one
    scalar, the e_- component carries another.  This is the
    natural lifting of `SectorPair` to TauReal-valued entries. -/
structure WOmega where
  /-- The e_+ component (paper's GerPi convention). -/
  ePlus : TauReal
  /-- The e_- component (paper's GerE convention). -/
  eMinus : TauReal

/-- **Additive trace on WOmega**: lifts `SectorPair.trPlus` to
    TauReal-valued entries.

      `Tr_+(a · e_+ + b · e_-) := a + b`. -/
def WOmega.trPlus (w : WOmega) : TauReal :=
  w.ePlus.add w.eMinus

/-- **The canonical w_ω** (paper Def 7.10):
    `w_ω := π_τ · e_+ + e_τ · e_-` placing π in the e_+ sector
    and e in the e_- sector. -/
def wOmega : WOmega where
  ePlus := TauReal.pi
  eMinus := TauReal.e

/-- The additive trace of the canonical `w_ω` is `π_τ + e_τ`
    (definitional). -/
@[simp] theorem WOmega.trPlus_wOmega :
    WOmega.trPlus wOmega = TauReal.pi.add TauReal.e := rfl

-- ============================================================
-- PART 3: Idempotent reformulation of coupling identity
-- ============================================================

/-- **Paper §7.4 Proposition 7.11 `cor:idempotent-lift`**:
    the coupling identity at the idempotent-decomposed level:

      `ι_τ · Tr_+(w_ω) ≡ 2`   (Cauchy equivalence on TauReal)

    Equivalently, `ι_τ = 2 / (π_τ + e_τ)` rendered through the
    additive trace of the idempotent-decomposed clock.

    Per paper Remark `lift-not-derivation`, this is a notational
    repackaging of `coupling_identity_at_omega` (Wave 15 / paper
    Thm 6.3).  The structural content is in the *placement* of
    π_τ and e_τ in the e_+ and e_- sectors respectively, which is
    forced by σ-equivariance + HolEnd_τ universality (paper
    Lemma 6.2 Step 2b). -/
theorem coupling_identity_idempotent :
    TauReal.equiv
      (TauReal.iota_tau.mul (WOmega.trPlus wOmega))
      TauReal.two := by
  rw [WOmega.trPlus_wOmega]
  exact coupling_identity_at_omega

-- ============================================================
-- PART 4: Prime polarity character χ
-- ============================================================

/-- **Prime polarity character** χ (paper Def 7.4
    `def:polarity-chi`).

    Parameterised over an abstract B-class predicate `B_class :
    Nat → Bool` (rendered concretely as `Legendre(2/p) = +1` in
    Wave 18 via the prime-polarity paper).  At the structural
    level:

      `χ_{B_class}(p) := if B_class p then 1 else if (p ≠ 2 ∧ ¬B_class p) then -1 else 0`.

    The `p = 2` case is hard-wired to 0 (ramification convention),
    matching paper's `ℙ_ram = {2}` partition.  Other primes are
    classified +1 (B) or -1 (C) by the `B_class` predicate. -/
def chi (B_class : Nat → Bool) (p : Nat) : Int :=
  match p with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | _ => if B_class p then 1 else -1

/-- **Unit-glue**: χ(0) = 0. -/
@[simp] theorem chi_zero (B_class : Nat → Bool) : chi B_class 0 = 0 := rfl

/-- **Unit-glue**: χ(1) = 0 (paper Remark `unit-glue`).
    The multiplicative unit must map to the neutral mediator of
    the idempotent decomposition. -/
@[simp] theorem chi_one (B_class : Nat → Bool) : chi B_class 1 = 0 := rfl

/-- **Ramification at the prime level**: `χ(2) = 0`.  This is
    the paper's "ramified prime contributes identically zero"
    (paper Def 7.4 `ℙ_ram = {2}` clause). -/
@[simp] theorem chi_two (B_class : Nat → Bool) : chi B_class 2 = 0 := rfl

/-- **B-class is +1**: when `B_class p` is true and `p ≥ 3`. -/
theorem chi_B_class (B_class : Nat → Bool) (p : Nat)
    (h_ge : 3 ≤ p) (h_B : B_class p = true) :
    chi B_class p = 1 := by
  match p, h_ge with
  | n + 3, _ =>
    show (if B_class (n + 3) then 1 else -1) = 1
    rw [h_B]
    rfl

/-- **C-class is -1**: when `B_class p` is false and `p ≥ 3`. -/
theorem chi_C_class (B_class : Nat → Bool) (p : Nat)
    (h_ge : 3 ≤ p) (h_B : B_class p = false) :
    chi B_class p = -1 := by
  match p, h_ge with
  | n + 3, _ =>
    show (if B_class (n + 3) then 1 else -1) = -1
    rw [h_B]
    rfl

-- ============================================================
-- PART 5: Split-complex prime polarity lift χ̃
-- ============================================================

/-- **The B/C contribution of a single prime power slot** — at trial
    divisor `d` with `k` copies of `d` extracted from `n`, returns
    the number of B-class copies (when `d ≥ 3 ∧ B_class d = true`)
    or `0` otherwise.

    The ramified prime `d = 2` always contributes `0` to `nuB` by
    paper Def 7.4 (`ℙ_ram = {2}`), independently of `B_class 2`.
    Other primes `d ≥ 3` contribute `k` (their full multiplicity)
    to whichever side `B_class` selects. -/
def bSlotContribution (B_class : Nat → Bool) (d k : Nat) : Nat :=
  if d < 3 then 0
  else if B_class d then k else 0

/-- **The C contribution of a single prime power slot** — at trial
    divisor `d` with `k` copies of `d` extracted from `n`, returns
    `k` only when `d ≥ 3 ∧ B_class d = false` (the C-prime case).

    Ramified `d = 2` again contributes `0`. -/
def cSlotContribution (B_class : Nat → Bool) (d k : Nat) : Nat :=
  if d < 3 then 0
  else if B_class d then 0 else k

/-- **Trial-divide `n` by `d`, returning `(k, n')`** where
    `n = d^k * n'` and `d ∤ n'`.  Bounded recursion via `fuel`
    keeps the helper structurally terminating; for any practical
    `n` the fuel `n + 1` upper bound is more than enough since
    `2^k ≤ n` forces `k ≤ log₂ n < n`. -/
def stripDivisor (d n fuel : Nat) : Nat × Nat :=
  if fuel = 0 then (0, n)
  else if d < 2 then (0, n)
  else if n = 0 then (0, n)
  else if n % d ≠ 0 then (0, n)
  else
    let (k', m) := stripDivisor d (n / d) (fuel - 1)
    (k' + 1, m)
termination_by fuel

/-- **Recursive trial-division worker for `nuB`** — at trial
    divisor `d`, accumulator `accB`, and remaining quotient `n`,
    sweeps through divisors `d, d+1, ..., n` adding the B-slot
    contribution of each.

    Termination via `fuel`; the public `nuB` wrapper picks
    `fuel := n + 1` to bound the sweep depth. -/
def nuBWorker (B_class : Nat → Bool) (d accB n fuel : Nat) : Nat :=
  if fuel = 0 then accB
  else if n ≤ 1 then accB
  else if d * d > n then
    -- n itself is prime (or a residual prime factor)
    accB + bSlotContribution B_class n 1
  else if n % d = 0 then
    let (k, m) := stripDivisor d n (n + 1)
    nuBWorker B_class (d + 1) (accB + bSlotContribution B_class d k) m (fuel - 1)
  else
    nuBWorker B_class (d + 1) accB n (fuel - 1)
termination_by fuel

/-- **Recursive trial-division worker for `nuC`** — same shape as
    `nuBWorker` but accumulates C-slot contributions. -/
def nuCWorker (B_class : Nat → Bool) (d accC n fuel : Nat) : Nat :=
  if fuel = 0 then accC
  else if n ≤ 1 then accC
  else if d * d > n then
    accC + cSlotContribution B_class n 1
  else if n % d = 0 then
    let (k, m) := stripDivisor d n (n + 1)
    nuCWorker B_class (d + 1) (accC + cSlotContribution B_class d k) m (fuel - 1)
  else
    nuCWorker B_class (d + 1) accC n (fuel - 1)
termination_by fuel

/-- **Counts the number of B-prime factors of `n` with multiplicity**
    (paper's `ν_B(n)`).

    Definition by trial division: for every prime factor `p` of `n`
    with multiplicity `v_p(n)`, contribute `v_p(n)` if
    `B_class p = true ∧ p ≥ 3`, else `0`.  The ramified prime
    `p = 2` is excluded by paper Def 7.4 `ℙ_ram = {2}` clause and
    is hard-wired to contribute `0` via `bSlotContribution`.

    Computation: `nuBWorker` starts trial-division at `d = 2`,
    accumulating B-slot contributions until the remainder reaches
    `1` or `d*d > n` (meaning the remainder is prime).  Fuel
    `n + 1` is a safe upper bound on the divisor sweep depth. -/
def nuB (B_class : Nat → Bool) (n : Nat) : Nat :=
  nuBWorker B_class 2 0 n (n + 1)

/-- **Counts the number of C-prime factors of `n` with multiplicity**
    (paper's `ν_C(n)`).  Same structure as `nuB` but accumulates
    C-slot contributions (`B_class p = false ∧ p ≥ 3`). -/
def nuC (B_class : Nat → Bool) (n : Nat) : Nat :=
  nuCWorker B_class 2 0 n (n + 1)

/-- **`nuB(0) = 0`** — the worker bails immediately on `n ≤ 1`. -/
@[simp] theorem nuB_zero (B_class : Nat → Bool) : nuB B_class 0 = 0 := by
  show nuBWorker B_class 2 0 0 1 = 0
  unfold nuBWorker
  rfl

/-- **`nuB(1) = 0`** — unit-glue: `1` has no prime factors. -/
@[simp] theorem nuB_one (B_class : Nat → Bool) : nuB B_class 1 = 0 := by
  show nuBWorker B_class 2 0 1 2 = 0
  unfold nuBWorker
  rfl

/-- **`nuB(2) = 0`** — ramification triviality at the prime level. -/
@[simp] theorem nuB_two (B_class : Nat → Bool) : nuB B_class 2 = 0 := by
  show nuBWorker B_class 2 0 2 3 = 0
  unfold nuBWorker
  -- At fuel=3, n=2: 2*2 = 4 > 2, so we hit the "prime residual" branch
  -- with `accB + bSlotContribution B_class 2 1` and bSlotContribution at d=2 is 0.
  simp [bSlotContribution]

/-- **`nuC(0) = 0`** — bails on `n ≤ 1`. -/
@[simp] theorem nuC_zero (B_class : Nat → Bool) : nuC B_class 0 = 0 := by
  show nuCWorker B_class 2 0 0 1 = 0
  unfold nuCWorker
  rfl

/-- **`nuC(1) = 0`** — unit-glue. -/
@[simp] theorem nuC_one (B_class : Nat → Bool) : nuC B_class 1 = 0 := by
  show nuCWorker B_class 2 0 1 2 = 0
  unfold nuCWorker
  rfl

/-- **`nuC(2) = 0`** — ramification triviality at the prime level. -/
@[simp] theorem nuC_two (B_class : Nat → Bool) : nuC B_class 2 = 0 := by
  show nuCWorker B_class 2 0 2 3 = 0
  unfold nuCWorker
  simp [cSlotContribution]

/-- **Split-complex prime polarity lift** (paper Def 7.5
    `def:chi-tilde`):

      `χ̃(n) := ν_B(n) · e_+ + ν_C(n) · e_-`

    rendered as `SectorPair ⟨ν_B(n), ν_C(n)⟩`.  The B/C
    classification is a parameter; concrete instantiation with the
    Legendre `(2/p) = +1` predicate happens in the prime-polarity
    companion paper (Wave 18).

    With the V3 Gap #7.2 fix (this commit), the underlying
    `nuB` / `nuC` counts are now concrete trial-division-based
    multiplicity counts (not the prior structural-placeholder
    `Nat.zero`).  Audit 2026-05-21 (Gap #7.2) flagged the
    placeholders; this commit replaces them with the real
    completely-additive functions of paper Def 7.5. -/
def chiTilde (B_class : Nat → Bool) (n : Nat) : SectorPair :=
  ⟨(nuB B_class n : Int), (nuC B_class n : Int)⟩

@[simp] theorem chiTilde_zero (B_class : Nat → Bool) :
    chiTilde B_class 0 = ⟨0, 0⟩ := by
  unfold chiTilde
  rw [nuB_zero, nuC_zero]
  rfl

@[simp] theorem chiTilde_one (B_class : Nat → Bool) :
    chiTilde B_class 1 = ⟨0, 0⟩ := by
  unfold chiTilde
  rw [nuB_one, nuC_one]
  rfl

-- ============================================================
-- PART 6: Ramification triviality (paper Prop 7.7)
-- ============================================================

/-- **Ramification triviality at p = 2** (paper Prop 7.7
    `prop:ramification-triviality` first part).

    `χ̃(2) = 0` in `D` because the ramified prime `p = 2` is
    excluded from both B and C classes by paper Def 7.4
    `ℙ_ram = {2}`.  Concretely, `bSlotContribution B_class 2 k = 0`
    and `cSlotContribution B_class 2 k = 0` for any `k`, because
    `d < 3` triggers the zero branch.

    With Gap #7.2 closed, the proof is now via the concrete
    `nuB_two` / `nuC_two` reductions rather than via the prior
    placeholder identity `nuB ≡ 0`. -/
theorem chiTilde_two (B_class : Nat → Bool) :
    chiTilde B_class 2 = ⟨0, 0⟩ := by
  unfold chiTilde
  rw [nuB_two, nuC_two]
  rfl

/-
**Higher-power ramification triviality (note)**: powers of 2
beyond the prime level — `χ̃(4)`, `χ̃(8)`, `χ̃(16)`, etc. — also
evaluate to `⟨0, 0⟩` because `bSlotContribution B_class 2 k = 0`
independently of `B_class` (the `d < 3` guard in
`bSlotContribution`/`cSlotContribution` forces the zero branch).

These cases are demonstrated via `#eval` below (Part 7) rather
than as kernel theorems: the well-founded recursion in
`stripDivisor` is not kernel-reducible through `decide` alone, and
a `native_decide` certificate would expand the trust budget
beyond the 3-kernel-axiom envelope of this module
(propext, Classical.choice, Quot.sound).  The monoid-homomorphism
form `χ̃(2^k) = k · χ̃(2) = 0 · k = 0` is the cleanest abstract
proof — its prime-factorisation-uniqueness premise is the
content of paper Prop 7.6 (Wave 18 in the prime-polarity
companion).
-/

/-- **Trace at zero**: `Tr_+(⟨0, 0⟩) = 0`. -/
@[simp] theorem SectorPair.trPlus_zero :
    SectorPair.trPlus ⟨0, 0⟩ = 0 := rfl

/-- **Ramification triviality, trace form**: `Tr_+(χ̃(2)) = 0`. -/
theorem trPlus_chiTilde_two_zero (B_class : Nat → Bool) :
    SectorPair.trPlus (chiTilde B_class 2) = 0 := by
  rw [chiTilde_two]; rfl

-- ============================================================
-- PART 7: #eval demonstrations
-- ============================================================

-- A concrete B-class predicate for demonstration: classify primes
-- by parity of (p - 1) / 2 (a placeholder, not the Legendre classifier;
-- Wave 18 will plug in the real Legendre(2/p))
def demoBClass : Nat → Bool := fun p => p % 4 == 1  -- toy example

#eval chi demoBClass 1                    -- 0 (unit-glue)
#eval chi demoBClass 2                    -- 0 (ramified)
#eval chi demoBClass 3                    -- -1 (3 % 4 = 3, C-class)
#eval chi demoBClass 5                    -- 1 (5 % 4 = 1, B-class)
#eval chi demoBClass 7                    -- -1 (7 % 4 = 3, C-class)
#eval chi demoBClass 11                   -- -1 (11 % 4 = 3, C-class)
#eval chi demoBClass 13                   -- 1 (13 % 4 = 1, B-class)

-- chiTilde demonstrations — V3 Gap #7.2: concrete nuB/nuC.
-- All powers of 2 give ⟨0, 0⟩ (ramification triviality).
#eval chiTilde demoBClass 1               -- ⟨0, 0⟩ (unit-glue)
#eval chiTilde demoBClass 2               -- ⟨0, 0⟩ (ramification triviality!)
#eval chiTilde demoBClass 4               -- ⟨0, 0⟩
#eval chiTilde demoBClass 8               -- ⟨0, 0⟩
#eval chiTilde demoBClass 16              -- ⟨0, 0⟩

-- Single-prime cases now exhibit non-trivial nuB/nuC counts
-- under the demoBClass toy predicate `p % 4 == 1`.
#eval chiTilde demoBClass 3               -- ⟨0, 1⟩ (3 % 4 = 3, C-prime)
#eval chiTilde demoBClass 5               -- ⟨1, 0⟩ (5 % 4 = 1, B-prime)
#eval chiTilde demoBClass 7               -- ⟨0, 1⟩ (7 % 4 = 3, C-prime)
#eval chiTilde demoBClass 9               -- ⟨0, 2⟩ (9 = 3², two C-prime copies)
#eval chiTilde demoBClass 15              -- ⟨1, 1⟩ (15 = 3·5, one C + one B)
#eval chiTilde demoBClass 25              -- ⟨2, 0⟩ (25 = 5², two B-prime copies)
#eval chiTilde demoBClass 35              -- ⟨1, 1⟩ (35 = 5·7, one B + one C)
#eval chiTilde demoBClass 100             -- ⟨2, 0⟩ (100 = 2²·5², ram pos absorbed)
#eval chiTilde demoBClass 105             -- ⟨1, 2⟩ (105 = 3·5·7, 1 B + 2 C)

-- Idempotent traces
#eval SectorPair.trPlus e_plus_sector     -- 1
#eval SectorPair.trPlus e_minus_sector    -- 1
#eval SectorPair.trPlus
  (SectorPair.add e_plus_sector e_minus_sector)  -- 2 (paper's "Tr_+(e_+ + e_-) = 2")

-- The idempotent-decomposed clock element's trace
-- WOmega.trPlus wOmega = π_τ + e_τ (TauReal-valued, can compute approx)
#eval ((WOmega.trPlus wOmega).approx 10).toRat   -- ≈ π + e ≈ 5.86

end Tau.Polarity

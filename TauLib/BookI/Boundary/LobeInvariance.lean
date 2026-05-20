import TauLib.BookI.Boundary.DefectInverseSystem

/-!
# TauLib.BookI.Boundary.LobeInvariance

**Critical-gap fill: paper `iota-tau/main.tex` §5.2 lobe-invariance
lemmas L1–L4, rendered as Lean theorems on the abstract
`DefectInverseSystem` scaffold.**

Paper §5.2 introduces a depth-`n` *polarity lattice* `Λ[n]` carrying:

- A **lobe-swap involution** `Swap_n : Λ[n] → Λ[n]` exchanging lobe
  labels `B ↔ C` and fixing the crossing-labelled class.
- A **transport functor** `Trans_n : Λ[n] → Λ[n]` propagating lobe
  labels along refinement-compatible paths.
- A **partial fusion operation**
  `Fuse_n : Λ[n] ×_× Λ[n] → Λ[n]` on classes meeting at the
  crossing anchor.
- A **crossing anchor** `a_n ∈ Λ[n]` — the unique class carrying
  the `×` label.

It then states four lemmas (L1–L4) needed for the non-polarity
half of the crossing-uniqueness argument:

| | Name | Statement (informal) |
|---|---|---|
| **L1** | transport closure | `Swap ∘ Trans = Trans ∘ Swap` |
| **L2** | fusion admissibility | `Swap (Fuse x y) = Fuse (Swap y) (Swap x)` (σ-twisted) |
| **L3** | associativity coherence | `Swap (Fuse (Fuse x y) z) = Fuse (Fuse (Swap z) (Swap y)) (Swap x)` |
| **L4** | anchor rigidity | `Swap a_n = a_n`, and `Swap x = x → x = a_n` |

Prior to this module these lemmas were **packaged as structure
fields** of `HolEndMorphismFull` (`preserves_NP` / `preserves_OA`)
rather than derived from a structural abstraction.  The audit
note at `audits/papers/2026-05-20-iota-tau-paper-V2-TauLib-backing-audit.md`
flagged this as Critical Gap #1.

This module supplies the abstract scaffold.  Concrete instance
witnesses on `TorusDefectSystem` and `refinementGrowingTorusSystem`
ship in the respective instance files (PART 9 of each).

## Registry Cross-References

- [I.D125] Tau.Boundary.DefectInverseSystem (Wave 12)
- [I.T-LobeL1] paper Lemma `lem:L1-transport` (transport closure)
- [I.T-LobeL2] paper Lemma `lem:L2-fusion` (fusion admissibility)
- [I.T-LobeL3] paper Lemma `lem:L3-assoc` (associativity coherence)
- [I.T-LobeL4] paper Lemma `lem:L4-anchor` (anchor rigidity)

## Mathematical content

### L1 — Transport closure (paper Lemma `lem:L1-transport`)

Paper claim: the transport functor commutes with the swap.  We
abstract a "transport" as **any σ-equivariant endomap** on
`defect_level n`.  L1 is then the *definition* of σ-equivariance:
`f (sigma_level n x) = sigma_level n (f x)`.

This is the *cleanest* form of L1 — the paper's "Trans is built
from `p_{n+1,n}` and `ℓ`, both σ-equivariant" reduces structurally
to: σ-equivariant maps compose σ-equivariantly.  We capture both
the predicate and its composition closure.

### L2 — Fusion admissibility (paper Lemma `lem:L2-fusion`)

Paper claim: σ preserves admissibility and intertwines fusion via
**order reversal**: `σ(Fuse(x,y)) = Fuse(σ(y), σ(x))`.

We abstract a "fusion" as a partial binary operation
`fuse : defect_level n → defect_level n → Option (defect_level n)`,
where `none` encodes inadmissibility.  L2 is then the predicate

  `∀ x y : defect_level n,
     Option.map (sigma_level n) (fuse x y) =
       fuse (sigma_level n y) (sigma_level n x)`

stating that σ intertwines fusion with the orientation reversal
on the operand pair.  Admissibility preservation follows from
the `Option.map`-form: `none ↦ none` mechanically, so σ-images of
inadmissible pairs remain inadmissible.

### L3 — Associativity coherence (paper Lemma `lem:L3-assoc`)

Paper claim: for admissible triples `(x, y, z)`,

  `σ(Fuse(Fuse(x,y), z)) = Fuse(Fuse(σ(z), σ(y)), σ(x))`.

**Proof structure** (paper §5.2 proof of L3, lines 1287–1293):
"expand both sides using L2 twice; the resulting coherence is the
lemniscate operad coherence."  Concretely:
1. By L2 applied to `(Fuse(x,y), z)`:
   `σ(Fuse(Fuse(x,y), z)) = Fuse(σ z, σ(Fuse(x,y)))`.
2. By L2 applied to `(x, y)`:
   `= Fuse(σ z, Fuse(σ y, σ x))`.
3. By **abstract associativity** of `Fuse`:
   `= Fuse(Fuse(σ z, σ y), σ x)`.

We render this with an abstract `FusionAssoc` hypothesis stating
`Option`-level associativity (both bracketings produce the same
`Option` result, including agreement on `none`).  In categorical
language, `FusionAssoc` says the fusion is associative on its
admissibility domain, which is the lemniscate-operad coherence
condition the paper invokes.

### L4 — Anchor rigidity (paper Lemma `lem:L4-anchor`)

Paper claim: `Swap a_n = a_n`, and every σ-fixed `x ≠ a_n` has
a length-`> 0` path to `a_n` in the refinement tree.

We abstract a "anchor" as a distinguished σ-fixed element, and
L4's uniqueness clause as the **paper's strict form**: every
σ-fixed element equals the anchor.  This matches concretely the
existing `TorusDefect.sigma_fixed_iff_crossing` and
`RefinedTorusDefect.sigma_fixed_iff_crossing` lemmas (Wave 14 and
Wave 19b respectively).

The "path length > 0 for non-anchor σ-fixed elements" clause is
**vacuous** when uniqueness holds, since there are no non-anchor
σ-fixed elements.  Strict uniqueness *implies* the path-length
claim.

## Public API

- `DefectInverseSystem.IsSigmaEquivariant` — paper's "σ-equivariant
  transport" predicate (L1 input).
- `DefectInverseSystem.IsSigmaEquivariant.id` / `.comp` —
  composition closure of L1's predicate.
- `DefectInverseSystem.LobeL1` — paper Lemma L1 in abstract form.
- `DefectInverseSystem.FusionAdmissibleSwap` — paper's L2 σ-twisted
  intertwining predicate.
- `DefectInverseSystem.LobeL2` — paper Lemma L2 (unfolded form).
- `DefectInverseSystem.LobeL2_admissibility` — admissibility
  preservation corollary.
- `DefectInverseSystem.FusionAssoc` — abstract `Option`-level
  associativity hypothesis.
- `DefectInverseSystem.LobeL3` — paper Lemma L3, derived from L2 +
  `FusionAssoc`.
- `DefectInverseSystem.AnchorRigidity` — paper's L4 strict
  uniqueness predicate.
- `DefectInverseSystem.LobeL4_swap_anchor` — paper Lemma L4 part (i).
- `DefectInverseSystem.LobeL4_uniqueness` — paper Lemma L4 part (ii).
- `DefectInverseSystem.LobeL4_no_other_fixed` — vacuity of the
  "non-anchor σ-fixed" set (strict form of part (ii)).

## Scope

`\scopetau`, **unconditional** at the abstract scaffold level.
The four lemmas hold on **any** concrete instance satisfying the
abstract hypotheses (`IsSigmaEquivariant` for L1,
`FusionAdmissibleSwap` for L2, `FusionAssoc` for L3,
`AnchorRigidity` for L4).  Concrete instance witnesses on
`TorusDefectSystem` and `refinementGrowingTorusSystem` ship in
the respective instance files (PART 9 of each).

This unblocks the paper's §5.2 sketch by exhibiting a structural
abstraction Lean can derive over; the **specific geometric**
content (constructing `Λ[n]` from the τ-circle presentation and
realising `Trans_n`, `Fuse_n` from the lemniscate operad) is
still deferred to future waves.  The abstract L1–L4 + concrete
instance witnesses bracket the paper-level content.
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

-- ============================================================
-- PART 1: L1 — σ-equivariant transport (paper Lemma 5.4)
-- ============================================================

/-- **σ-equivariance predicate** on an endomap of a defect level
    (paper §5.2 setup for L1).

    `f : defect_level n → defect_level n` is σ-equivariant iff
    it commutes with `sigma_level n`:

      `f (σ x) = σ (f x)`.

    Paper's transport functor `Trans_n` is built from canonical
    projection `p_{n+1,n}` and lobe label `ℓ`, both σ-equivariant
    (paper §5.2 proof of L1).  We render the structural content
    as this predicate. -/
def DefectInverseSystem.IsSigmaEquivariant
    (D : DefectInverseSystem) (n : Nat)
    (f : D.defect_level n → D.defect_level n) : Prop :=
  ∀ x : D.defect_level n,
    f (D.sigma_level n x) = D.sigma_level n (f x)

/-- **Identity is σ-equivariant** — trivial witness for the L1
    predicate. -/
theorem DefectInverseSystem.IsSigmaEquivariant.id
    (D : DefectInverseSystem) (n : Nat) :
    D.IsSigmaEquivariant n (fun x => x) :=
  fun _ => rfl

/-- **Composition of σ-equivariant maps is σ-equivariant**
    (paper §5.2: "Trans is built from σ-equivariant pieces, hence
    σ-equivariant"). -/
theorem DefectInverseSystem.IsSigmaEquivariant.comp
    {D : DefectInverseSystem} {n : Nat}
    {f g : D.defect_level n → D.defect_level n}
    (hf : D.IsSigmaEquivariant n f)
    (hg : D.IsSigmaEquivariant n g) :
    D.IsSigmaEquivariant n (f ∘ g) := by
  intro x
  show f (g (D.sigma_level n x)) = D.sigma_level n (f (g x))
  rw [hg x, hf (g x)]

/-- **Paper Lemma L1 (transport closure, `lem:L1-transport`)**:
    a σ-equivariant transport functor commutes with the lobe-swap.

    Rendered as: `σ (f x) = f (σ x)` (the symmetric of the
    `IsSigmaEquivariant` definition).  Paper's
    "`Swap ∘ Trans = Trans ∘ Swap`" is precisely this identity. -/
theorem DefectInverseSystem.LobeL1
    {D : DefectInverseSystem} {n : Nat}
    {f : D.defect_level n → D.defect_level n}
    (hf : D.IsSigmaEquivariant n f) (x : D.defect_level n) :
    D.sigma_level n (f x) = f (D.sigma_level n x) :=
  (hf x).symm

-- ============================================================
-- PART 2: L2 — Fusion admissibility (paper Lemma 5.5)
-- ============================================================

/-- **σ-twisted fusion intertwining predicate** (paper §5.2 L2
    setup).

    A partial binary operation
    `fuse : defect_level n → defect_level n → Option (defect_level n)`
    is **σ-twisted-equivariant** iff applying σ to the fusion
    result equals fusing the σ-images in *reversed* order:

      `Option.map σ (fuse x y) = fuse (σ y) (σ x)`.

    The `Option` wrapper encodes admissibility: `none` means
    inadmissible pair, and `none` maps to `none` under
    `Option.map`, so inadmissibility is preserved by σ
    automatically.

    The order reversal `(x, y) ↦ (σ y, σ x)` is paper's
    "σ reverses the orientation of the crossing-point chart"
    (Book I ch. 40.3 reference, paper line 1274). -/
def DefectInverseSystem.FusionAdmissibleSwap
    (D : DefectInverseSystem) (n : Nat)
    (fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n)) : Prop :=
  ∀ (x y : D.defect_level n),
    Option.map (D.sigma_level n) (fuse x y) =
      fuse (D.sigma_level n y) (D.sigma_level n x)

/-- **Paper Lemma L2 (fusion admissibility, `lem:L2-fusion`)** —
    unfolded form.

    Given the σ-twisted intertwining predicate, the identity holds
    for every operand pair.  Admissibility preservation is built
    in via `Option.map`: if `fuse x y = none` (inadmissible),
    then `fuse (σ y) (σ x) = Option.map σ none = none` (still
    inadmissible). -/
theorem DefectInverseSystem.LobeL2
    {D : DefectInverseSystem} {n : Nat}
    {fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n)}
    (hfuse : D.FusionAdmissibleSwap n fuse)
    (x y : D.defect_level n) :
    Option.map (D.sigma_level n) (fuse x y) =
      fuse (D.sigma_level n y) (D.sigma_level n x) :=
  hfuse x y

/-- **Admissibility preservation under σ** — corollary of L2.

    If a pair `(x, y)` is inadmissible (`fuse x y = none`), then
    so is the σ-reversed pair `(σ y, σ x)`. -/
theorem DefectInverseSystem.LobeL2_admissibility
    {D : DefectInverseSystem} {n : Nat}
    {fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n)}
    (hfuse : D.FusionAdmissibleSwap n fuse)
    (x y : D.defect_level n) (h_none : fuse x y = none) :
    fuse (D.sigma_level n y) (D.sigma_level n x) = none := by
  rw [← hfuse x y, h_none]; rfl

/-- **Symmetric form of L2** — convenient rewriting form with
    σ on the outside. -/
theorem DefectInverseSystem.LobeL2_symm
    {D : DefectInverseSystem} {n : Nat}
    {fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n)}
    (hfuse : D.FusionAdmissibleSwap n fuse)
    (x y : D.defect_level n) :
    fuse (D.sigma_level n y) (D.sigma_level n x) =
      Option.map (D.sigma_level n) (fuse x y) :=
  (hfuse x y).symm

-- ============================================================
-- PART 3: L3 — Associativity coherence (paper Lemma 5.6)
-- ============================================================

/-- **Left-bracketed three-fold fusion** — `Fuse(Fuse(x, y), z)`.

    Encodes paper's left-associated triple fusion with explicit
    handling of partiality via `Option.bind`: if `fuse x y =
    none` (inadmissible inner pair), the entire expression is
    `none`. -/
def DefectInverseSystem.fuseLeft
    {D : DefectInverseSystem} {n : Nat}
    (fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n))
    (x y z : D.defect_level n) :
    Option (D.defect_level n) :=
  (fuse x y).bind (fun w => fuse w z)

/-- **Right-bracketed three-fold fusion** — `Fuse(x, Fuse(y, z))`.

    Symmetric counterpart of `fuseLeft`, with `(y, z)` resolved
    first.  Paper's L3 implicitly uses both bracketings; we
    expose both for the associativity hypothesis. -/
def DefectInverseSystem.fuseRight
    {D : DefectInverseSystem} {n : Nat}
    (fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n))
    (x y z : D.defect_level n) :
    Option (D.defect_level n) :=
  (fuse y z).bind (fun w => fuse x w)

/-- **`Option`-level associativity of a partial fusion** — abstract
    hypothesis for L3.

    States that for all admissible triples, the two bracketings
    agree (including on the `none` results, which encode
    inadmissibility).  Paper's "lemniscate operad coherence
    relation" (line 1290) is this hypothesis in operadic form. -/
def DefectInverseSystem.FusionAssoc
    (D : DefectInverseSystem) (n : Nat)
    (fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n)) : Prop :=
  ∀ (x y z : D.defect_level n),
    D.fuseLeft fuse x y z = D.fuseRight fuse x y z

/-- **Auxiliary: σ of a left-fused triple equals right-fused
    σ-reversed triple.**

    Pure L2-twice application — no `FusionAssoc` needed.  This is
    the *intermediate* form of paper's L3, before applying
    associativity to convert right-bracketing to left-bracketing
    on the RHS. -/
theorem DefectInverseSystem.lobeL3_intermediate
    {D : DefectInverseSystem} {n : Nat}
    {fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n)}
    (hfuse : D.FusionAdmissibleSwap n fuse)
    (x y z : D.defect_level n) :
    Option.map (D.sigma_level n) (D.fuseLeft fuse x y z) =
      D.fuseRight fuse (D.sigma_level n z) (D.sigma_level n y)
                       (D.sigma_level n x) := by
  -- Unfold fuseLeft on LHS, fuseRight on RHS.
  show Option.map (D.sigma_level n)
        ((fuse x y).bind (fun w => fuse w z)) =
       (fuse (D.sigma_level n y) (D.sigma_level n x)).bind
         (fun w => fuse (D.sigma_level n z) w)
  -- Case-split on the inner fuse x y.
  cases h_inner : fuse x y with
  | none =>
    -- LHS: Option.map σ (none.bind _) = Option.map σ none = none
    simp
    -- RHS: fuse (σ y) (σ x) = Option.map σ (fuse x y) = Option.map σ none = none
    have : fuse (D.sigma_level n y) (D.sigma_level n x) = none := by
      rw [← hfuse x y, h_inner]; rfl
    rw [this]; rfl
  | some w =>
    -- LHS: Option.map σ ((some w).bind (fun w => fuse w z))
    --    = Option.map σ (fuse w z)
    -- RHS: (fuse (σ y) (σ x)).bind (fun u => fuse (σ z) u)
    -- By L2: fuse (σ y) (σ x) = Option.map σ (fuse x y) = Option.map σ (some w) = some (σ w)
    -- So RHS = (some (σ w)).bind _ = fuse (σ z) (σ w)
    -- By L2: fuse (σ z) (σ w) = Option.map σ (fuse w z)  [applied to (w, z)]
    -- Hence LHS = RHS.
    have h_fuse_σ : fuse (D.sigma_level n y) (D.sigma_level n x) =
                    some (D.sigma_level n w) := by
      rw [← hfuse x y, h_inner]; rfl
    have h_wz : Option.map (D.sigma_level n) (fuse w z) =
                fuse (D.sigma_level n z) (D.sigma_level n w) := hfuse w z
    simp [h_fuse_σ]
    exact h_wz

/-- **Paper Lemma L3 (associativity, `lem:L3-assoc`)** —
    σ-equivariant left-associative coherence.

    Given a partial fusion `fuse` satisfying L2
    (`FusionAdmissibleSwap`) and `Option`-level associativity
    (`FusionAssoc`):

      `Option.map σ (fuseLeft fuse x y z) =
         fuseLeft fuse (σ z) (σ y) (σ x)`,

    i.e. swap distributes over left-bracketed fusion with the
    triple-order reversal `(x, y, z) ↦ (σ z, σ y, σ x)`.

    **Proof**:
    1. By `lobeL3_intermediate` (pure L2 twice):
       `σ (fuseLeft fuse x y z) = fuseRight fuse (σ z) (σ y) (σ x)`.
    2. By `FusionAssoc` applied to `(σ z, σ y, σ x)`:
       `fuseRight fuse (σ z) (σ y) (σ x) =
          fuseLeft fuse (σ z) (σ y) (σ x)`.
    Compose.

    Paper §5.2 proof of L3 (lines 1287–1293): "expand both sides
    using L2 twice; the resulting coherence is the lemniscate
    operad coherence relation, which holds at every finite stage
    by direct case analysis."  Our `FusionAssoc` *is* the operad
    coherence relation, rendered at the `Option`-level. -/
theorem DefectInverseSystem.LobeL3
    {D : DefectInverseSystem} {n : Nat}
    {fuse : D.defect_level n → D.defect_level n →
              Option (D.defect_level n)}
    (hfuse : D.FusionAdmissibleSwap n fuse)
    (hassoc : D.FusionAssoc n fuse)
    (x y z : D.defect_level n) :
    Option.map (D.sigma_level n) (D.fuseLeft fuse x y z) =
      D.fuseLeft fuse (D.sigma_level n z) (D.sigma_level n y)
                       (D.sigma_level n x) := by
  rw [D.lobeL3_intermediate hfuse x y z]
  exact (hassoc (D.sigma_level n z) (D.sigma_level n y)
                 (D.sigma_level n x)).symm

-- ============================================================
-- PART 4: L4 — Anchor rigidity (paper Lemma 5.7)
-- ============================================================

/-- **Anchor rigidity predicate** (paper §5.2 L4 setup).

    A distinguished element `a` of `defect_level n` is a **rigid
    anchor** iff:
    1. `a` is σ-fixed: `sigma_level n a = a`.
    2. **Strict uniqueness**: every σ-fixed element equals `a`.

    Paper's L4 originally states (i) `Swap a_n = a_n` and (ii)
    "for every `x` with `Swap x = x` and `x ≠ a_n`, the path
    from `x` to `a_n` has length `> 0`."

    Our strict-uniqueness form *strengthens* (ii) to: there are
    no σ-fixed `x` other than `a_n`, making the path-length
    claim vacuous.  The paper's proof of (ii) (lines 1303–1313)
    is *exactly* this argument: "any σ-fixed `x` with a lobe
    label would be swapped with a counterpart in the opposite
    lobe, contradicting `Swap x = x` unless `x` is itself
    crossing-labelled."  Strict uniqueness *is* the conclusion
    of that argument.

    This matches concretely the existing
    `TorusDefect.sigma_fixed_iff_crossing` and
    `RefinedTorusDefect.sigma_fixed_iff_crossing` lemmas. -/
structure DefectInverseSystem.AnchorRigidity
    (D : DefectInverseSystem) (n : Nat) where
  /-- The distinguished crossing anchor `a_n`. -/
  anchor : D.defect_level n
  /-- The anchor is σ-fixed. -/
  anchor_fixed : D.sigma_level n anchor = anchor
  /-- **Strict uniqueness**: every σ-fixed element equals `anchor`. -/
  uniqueness : ∀ (x : D.defect_level n),
    D.sigma_level n x = x → x = anchor

/-- **Paper Lemma L4 part (i)** (`lem:L4-anchor`, line 1304):
    `Swap a_n = a_n`. -/
theorem DefectInverseSystem.LobeL4_swap_anchor
    {D : DefectInverseSystem} {n : Nat}
    (h : D.AnchorRigidity n) :
    D.sigma_level n h.anchor = h.anchor :=
  h.anchor_fixed

/-- **Paper Lemma L4 part (ii)** (`lem:L4-anchor`, lines 1305–1313)
    in strict-uniqueness form: every σ-fixed element equals the
    anchor.

    This is the *contrapositive-strengthening* of paper's "path
    length > 0 for non-anchor σ-fixed" clause: the set of
    non-anchor σ-fixed elements is empty, so the path-length
    claim is vacuously true. -/
theorem DefectInverseSystem.LobeL4_uniqueness
    {D : DefectInverseSystem} {n : Nat}
    (h : D.AnchorRigidity n)
    (x : D.defect_level n) (h_fix : D.sigma_level n x = x) :
    x = h.anchor :=
  h.uniqueness x h_fix

/-- **Vacuity of non-anchor σ-fixed elements** — direct
    consequence of `LobeL4_uniqueness`.

    Paper's "for every `x` with `Swap x = x` and `x ≠ a_n`, the
    path from `x` to `a_n` has length `> 0`" reduces to this
    vacuity: the universally-quantified hypothesis is never
    satisfied, so the conclusion holds trivially. -/
theorem DefectInverseSystem.LobeL4_no_other_fixed
    {D : DefectInverseSystem} {n : Nat}
    (h : D.AnchorRigidity n)
    (x : D.defect_level n)
    (h_fix : D.sigma_level n x = x) (h_neq : x ≠ h.anchor) :
    False :=
  h_neq (h.uniqueness x h_fix)

-- ============================================================
-- PART 5: Bundled lobe-invariance data
-- ============================================================

/-- **Full lobe-invariance package** (paper §5.2 L1–L4 bundled).

    Combines:
    - A σ-equivariant transport `trans` (L1 input).
    - A σ-twisted-equivariant fusion `fuse` (L2 input).
    - `Option`-level associativity (L3 input).
    - An anchor rigidity witness (L4 input).

    Consumers obtaining a `LobeInvariance D n` automatically get
    all four lobe-invariance lemmas L1–L4 in derived form.

    Convenience structure for downstream consumers (e.g. concrete
    instance files; the paper §5 NP-half proof uses all four
    lemmas together). -/
structure DefectInverseSystem.LobeInvariance
    (D : DefectInverseSystem) (n : Nat) where
  /-- The σ-equivariant transport functor (paper `Trans_n`). -/
  trans : D.defect_level n → D.defect_level n
  /-- L1 input: `trans` is σ-equivariant. -/
  trans_sigma_eq : D.IsSigmaEquivariant n trans
  /-- The partial fusion operation (paper `Fuse_n`). -/
  fuse : D.defect_level n → D.defect_level n →
           Option (D.defect_level n)
  /-- L2 input: fusion is σ-twisted-equivariant. -/
  fuse_sigma_swap : D.FusionAdmissibleSwap n fuse
  /-- L3 input: fusion is associative on its admissibility domain. -/
  fuse_assoc : D.FusionAssoc n fuse
  /-- L4 input: rigid anchor data. -/
  anchor_rigid : D.AnchorRigidity n

end Tau.Boundary

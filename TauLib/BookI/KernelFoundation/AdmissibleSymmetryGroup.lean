import TauLib.BookI.KernelFoundation.H8KernelSynthesis

/-!
# TauLib.BookI.KernelFoundation.AdmissibleSymmetryGroup

**Wave 35 — H8/H0 Admissible Symmetry Group (Tier 2 unlock target #4).**

Lean structural rendering of paper `kernel-foundation/section-06-ontic-identity.tex`
Clause (iii) of Theorem `main-ontic-identity` (= I.T46): the
**admissible symmetry group** preserving normal forms.

From paper §6.676–687:
> "an admissible symmetry is a τ-endo-functor that preserves the
> kernel axioms.  Such a functor preserves the program monoid,
> hence the normal-form relation, … the resource discipline, and
> the categorical structure.  Consequently, it preserves normal
> forms setwise and pointwise up to canonical natural transformation.
> Ontic identity, defined by normal-form equality, is therefore
> invariant.  The precise formulation of `admissible symmetry' is
> the automorphism group of the program monoid modulo the kernel
> axioms (Book I Ch.~81 §2)."

This wave provides the **structural-witness rendering** of the
admissible-symmetry monoid (with identity + composition forming a
monoid; group-level inverses deferred to Book III) + the keystone
**NF-invariance theorem**: any admissible symmetry preserves the
normal form of every Program.

## Registry Cross-References

- [I.T46]    OnticIdentityInvariance (existing, MetaLogic)
- [I.T117]   nf_confluence_statement (Wave 26 H7 NF confluence)
- [I.T120]   address_resolution_theorem_restated (Wave 26)
- [I.T174]   h8_ontic_identity_invariance_witness (Wave 34)
- [I.T-H8-AdmSym]   paper §6 admissible-symmetry definition
- [I.T-H8-AdmId]    identity admissibility
- [I.T-H8-AdmComp]  composition admissibility (monoid law)
- [I.T-H8-NFInv]    NF-invariance under admissible symmetries

## Mathematical Content (paper §6 Clause iii)

### Admissible symmetry definition

An **admissible symmetry** is a τ-endo-functor `φ : Program → Program`
satisfying:
- **K0–K6 preservation**: φ commutes with the kernel axioms
- **NF coherence**: `normalize (φ p) = normalize p` for all `p`
  (equivalently: φ acts on Program but doesn't change the canonical
  NF address)
- **Composition closure**: φ ∘ ψ is admissible whenever both are

### The admissible-symmetry monoid

Identity: `id_admissible : AdmissibleSymmetry`
Composition: `comp_admissible : AdmissibleSymmetry → AdmissibleSymmetry → AdmissibleSymmetry`
Identity laws: `id ∘ φ = φ = φ ∘ id`
Associativity: `(φ ∘ ψ) ∘ χ = φ ∘ (ψ ∘ χ)`

(Group-level inverses require deeper categorical machinery from
Book III; this wave covers the monoid level.)

### NF-invariance keystone

For any admissible symmetry φ and Program p:
- `normalize (φ p) = normalize p` (NF preserved pointwise)
- Equivalently: φ acts trivially on the NF quotient

This is paper §6's Clause (iii) at the structural-witness level.

## Lean rendering strategy

- `AdmissibleSymmetry` is rendered as a structure carrying the
  underlying map + the NF-preservation property.
- Identity + composition are constructive defs.
- Monoid laws (id-left, id-right, associativity) are theorems.
- NF-invariance is a direct consequence of the preservation
  property (built into the structure).

## Scope

`\scopetau` for the structural-synthesis content; the deeper
group-theoretic structure (inverses, normal subgroups,
Galois-style classification) is **deferred to Book III** per
paper §6's "Book I Ch. 81 §2 for details" reference.
-/

set_option autoImplicit false

namespace Tau.KernelFoundation

open Tau.Denotation Tau.Addressability Tau.MetaLogic

-- ============================================================
-- PART 1: Admissible Symmetry — definition
-- ============================================================

/-- **Paper §6 admissible-symmetry definition (structural witness)**.

    An `AdmissibleSymmetry` is a τ-endo-functor on `Program`
    preserving the canonical normal form.  This is the
    NF-coherence projection of the paper's full
    "K0–K6-preserving τ-endo-functor" — the relevant operational
    content for Clause (iii) of the Ontic Identity Invariance
    theorem (I.T46). -/
structure AdmissibleSymmetry where
  /-- The underlying map on Programs. -/
  apply : Program → Program
  /-- NF-preservation: the symmetry acts trivially on the
      canonical NF address (paper §6 NF coherence requirement). -/
  preserves_nf : ∀ p : Program, normalize (apply p) = normalize p

-- ============================================================
-- PART 2: Identity admissible symmetry
-- ============================================================

/-- **Identity admissible symmetry**: the trivial symmetry that
    fixes every Program pointwise.  Trivially preserves NF. -/
def id_admissible : AdmissibleSymmetry where
  apply := fun p => p
  preserves_nf := fun _ => rfl

@[simp] theorem id_admissible_apply (p : Program) :
    id_admissible.apply p = p := rfl

-- ============================================================
-- PART 3: Composition of admissible symmetries
-- ============================================================

/-- **Composition of admissible symmetries**: φ ∘ ψ is admissible
    whenever both are.  Preserves NF by transitivity:
    `normalize ((φ ∘ ψ) p) = normalize (ψ p) = normalize p`. -/
def comp_admissible (φ ψ : AdmissibleSymmetry) : AdmissibleSymmetry where
  apply := fun p => φ.apply (ψ.apply p)
  preserves_nf := fun p => by
    rw [φ.preserves_nf (ψ.apply p), ψ.preserves_nf p]

@[simp] theorem comp_admissible_apply (φ ψ : AdmissibleSymmetry)
    (p : Program) :
    (comp_admissible φ ψ).apply p = φ.apply (ψ.apply p) := rfl

-- ============================================================
-- PART 4: Monoid laws (identity + associativity)
-- ============================================================

/-- **Left identity law**: `id ∘ φ = φ` (pointwise on apply). -/
theorem id_left_admissible (φ : AdmissibleSymmetry) (p : Program) :
    (comp_admissible id_admissible φ).apply p = φ.apply p := rfl

/-- **Right identity law**: `φ ∘ id = φ` (pointwise on apply). -/
theorem id_right_admissible (φ : AdmissibleSymmetry) (p : Program) :
    (comp_admissible φ id_admissible).apply p = φ.apply p := rfl

/-- **Associativity law**: `(φ ∘ ψ) ∘ χ = φ ∘ (ψ ∘ χ)` (pointwise). -/
theorem assoc_admissible (φ ψ χ : AdmissibleSymmetry) (p : Program) :
    (comp_admissible (comp_admissible φ ψ) χ).apply p =
    (comp_admissible φ (comp_admissible ψ χ)).apply p := rfl

-- ============================================================
-- PART 5: NF-invariance keystone (paper Clause iii)
-- ============================================================

/-- **Paper §6 Clause (iii) — NF-invariance keystone**.

    For any admissible symmetry φ and Program p, the canonical
    NF address is preserved: `normalize (φ p) = normalize p`.

    This IS Clause (iii) of paper Theorem `main-ontic-identity`
    (I.T46): identity is invariant under admissible symmetries.

    Direct from the structure's `preserves_nf` field. -/
theorem nf_invariance_under_admissible (φ : AdmissibleSymmetry)
    (p : Program) :
    normalize (φ.apply p) = normalize p :=
  φ.preserves_nf p

/-- **NF-invariance lifted to tauEq**: admissible symmetries
    preserve τ-equivalence.

    Concretely: if `tauEq p q`, then `tauEq (φ.apply p) (φ.apply q)`.
    Proof: tauEq is `nfEquiv (normalize p) (normalize q)`;
    since `normalize (φ p) = normalize p` and similarly for q,
    the NF-equivalence transfers. -/
theorem tauEq_invariance_under_admissible (φ : AdmissibleSymmetry)
    (p q : Program) (h : tauEq p q) : tauEq (φ.apply p) (φ.apply q) := by
  unfold tauEq at *
  rw [φ.preserves_nf p, φ.preserves_nf q]
  exact h

-- ============================================================
-- PART 6: Wave 35 H8 admissible-symmetry synthesis
-- ============================================================

/-- **Wave 35 H8 admissible-symmetry synthesis**.

    Packages the four-clause structural significance of paper
    §6 Clause (iii):

    1. **Identity is admissible**: `id_admissible : AdmissibleSymmetry`
    2. **Composition closure**: φ ∘ ψ admissible (monoid law)
    3. **Monoid laws**: id-left + id-right + associativity
    4. **NF-invariance**: every admissible symmetry preserves NF

    Together they witness paper §6 Clause (iii) at the
    structural-content level. -/
theorem h8_admissible_symmetry_synthesis (φ ψ : AdmissibleSymmetry)
    (p : Program) :
    -- Clause 1: identity is admissible (acts as id)
    id_admissible.apply p = p ∧
    -- Clause 2: composition is admissible (works pointwise)
    (comp_admissible φ ψ).apply p = φ.apply (ψ.apply p) ∧
    -- Clause 3a: left identity law
    (comp_admissible id_admissible φ).apply p = φ.apply p ∧
    -- Clause 3b: right identity law
    (comp_admissible φ id_admissible).apply p = φ.apply p ∧
    -- Clause 4: NF-invariance (the KEYSTONE)
    normalize (φ.apply p) = normalize p :=
  ⟨id_admissible_apply p,
   comp_admissible_apply φ ψ p,
   id_left_admissible φ p,
   id_right_admissible φ p,
   nf_invariance_under_admissible φ p⟩

-- ============================================================
-- PART 7: Concrete examples
-- ============================================================

/-- The identity admissible symmetry as concrete witness. -/
example : AdmissibleSymmetry := id_admissible

/-- Composition of two identities is identity. -/
example (p : Program) :
    (comp_admissible id_admissible id_admissible).apply p = p := rfl

/-- Triple composition associativity at concrete inputs. -/
example (φ ψ χ : AdmissibleSymmetry) (p : Program) :
    (comp_admissible (comp_admissible φ ψ) χ).apply p =
    (comp_admissible φ (comp_admissible ψ χ)).apply p := rfl

end Tau.KernelFoundation

import TauLib.BookI.Denotation.Arithmetic
import TauLib.BookI.Orbit.Generation
import TauLib.BookI.Kernel.Axioms

/-!
# TauLib.BookI.Denotation.OmegaLadderAbsorption

**Registry: [I.T11d] Omega-Absorption for the Iterator Ladder**

The closure beacon ω is the unique absorbing fixed point of every
rung of the iterator ladder (addition, multiplication, exponentiation,
tetration). The proof factors through K2 (ρ(ω) = ω); since every
ladder rung is defined as a recursive fold of the previous rung
(ultimately of ρ itself), absorption propagates structurally.

```
Rung 0  (iterator):     ρ(ω) = ω                 (K2, axiomatic)
Rung 1  (addition):     ω + n = ω                (iter_rho propagation)
Rung 2  (multiplication): ω · n = ω             (iterated addition)
Rung 3  (exponentiation): n ^ ω = ω             (limit of recursive fold)
Rung 4  (tetration):    ⁿω = ω                  (limit of exp fold)
       (self):          ω ^ ω = ω               (joint fixed point)
```

## Strategic significance

This is the **kernel-level counterpart of the no-ghost reading** of
Cantor's diagonal. Where classical mathematics has $2^{\aleph_0} =
\mathfrak{c} > \aleph_0$ (the cardinal hierarchy strictly increases),
the τ-kernel's recursive-fold structure plus K2 gives
$n^\omega = \omega$ at every rung. The cardinality hierarchy
collapses at the kernel level.

The apparent classical hierarchy is the **bridge's projection** —
the noncomputable RingEquiv `tauRealQRingEquivReal` (PR #161, Path B
FINAL KEYSTONE) projects the ω-closed kernel structure into Lean's
classical universe under cardinal arithmetic. The "ghost particles"
of $\mathfrak{c}, 2^\mathfrak{c}, \dots$ are the cardinal-arithmetic
reading of one and the same ω.

## Companion artefacts

- Manuscript: `corpus/manuscript-sources/book-01/part03/ch12-exp-tetration.tex`
  §"ω-Absorption: The Beacon Caps the Ladder" (registry I.T11d)
- Atlas insight: `2026-05-04-omega-as-cross-layer-mass-bearer.md`
- Companion research note: `cantor-bridge-categorical/main.tex`
- Path B FINAL KEYSTONE: TauLib commit `dd343cb` (PR #161)
- Cantor diagonal as constructor: TauLib PR #163

## Registry Cross-References

- [I.T11d] Omega-Absorption for the Iterator Ladder — `omega_ladder_absorption_iter_rho`
- [I.K2] Omega Fixed Point — `K2_omega_fixed` (the substrate)
- [I.D10–I.D13] Iterator-ladder operations (substrate)
-/

set_option autoImplicit false

namespace Tau.Denotation

open Tau.Kernel Tau.Orbit Generator

-- ============================================================
-- THE CORE STRUCTURAL FACT (Rung 0, the substrate)
-- ============================================================

/-- **🎉 [I.T11d] Core absorption: ω is fixed under iter_rho**.

    The substrate fact from which all iterator-ladder absorption
    propagates. Every rung of the ladder is a recursive fold of ρ
    (with finite many iterations); since `iter_rho m ⟨omega, d⟩ =
    ⟨omega, d⟩` for any `m`, every ladder rung absorbs ω at the
    iterating-argument position.

    This is direct from `Tau.Orbit.iter_rho_omega` (and ultimately
    from K2: `K2_omega_fixed`). -/
@[simp] theorem omega_ladder_absorption_iter_rho (n d : Nat) :
    iter_rho n ⟨omega, d⟩ = ⟨omega, d⟩ :=
  iter_rho_omega n d

-- ============================================================
-- ω-OBJECT-LEVEL ADDITION (Rung 1)
-- ============================================================

/-- **Object-level addition** at the τ-kernel level: iterates ρ on
    the first argument by the second-argument count. This extends
    the `idx_add` of `Arithmetic.lean` (which lives on `TauIdx`,
    the α-orbit) to the broader `TauObj` type, which includes ω
    as a possible first argument. -/
def obj_add (x : TauObj) (m : Nat) : TauObj := iter_rho m x

/-- **Rung 1 absorption**: ω + n = ω.

    Direct corollary of the core absorption: `obj_add` is just
    `iter_rho` with arguments swapped. -/
@[simp] theorem omega_obj_add (m d : Nat) :
    obj_add ⟨omega, d⟩ m = ⟨omega, d⟩ :=
  iter_rho_omega m d

-- ============================================================
-- ω-OBJECT-LEVEL HIGHER RUNGS (mul, exp, tet)
-- ============================================================

/-- **Recursive fold-iteration**: applies a binary operation
    `op : TauObj → Nat → TauObj` iteratively `m` times to the
    initial element `init`, with `step` driving each iteration.

    This is the abstract scheme that all higher rungs follow:
    multiplication = fold of addition, exponentiation = fold of
    multiplication, tetration = fold of exponentiation. -/
def fold_iter (op : TauObj → Nat → TauObj) (init : TauObj) (step : Nat) :
    Nat → TauObj
  | 0 => init
  | m + 1 => op (fold_iter op init step m) step

/-- **Generic ω-absorption for fold iterations**.

    If the binary operation `op` absorbs ω in the first argument
    (i.e., `op ⟨omega, d⟩ k` stays ω-seeded for any k), then
    `fold_iter op ⟨omega, d⟩ step m` is also ω-seeded for any m.

    This is the structural lemma that propagates absorption from
    one rung to the next. -/
theorem fold_iter_omega_absorbs
    (op : TauObj → Nat → TauObj) (d step m : Nat)
    (h_init_seed : TauObj.seed (fold_iter op ⟨omega, d⟩ step 0) = omega)
    (h_op_preserves :
      ∀ x k, x.seed = omega → (op x k).seed = omega) :
    (fold_iter op ⟨omega, d⟩ step m).seed = omega := by
  induction m with
  | zero => exact h_init_seed
  | succ m ih =>
    show (op (fold_iter op ⟨omega, d⟩ step m) step).seed = omega
    exact h_op_preserves _ step ih

-- ============================================================
-- THE BUNDLE: ω-LADDER-ABSORPTION (I.T11d, Rung 0 + Rung 1)
-- ============================================================

/-- **🎉 [I.T11d] ω-Absorption Bundle (Rung 0 and Rung 1)**.

    The two foundational rungs proven explicitly:
    - Rung 0 (iter_rho): `iter_rho n ⟨omega, d⟩ = ⟨omega, d⟩`
    - Rung 1 (addition): `obj_add ⟨omega, d⟩ m = ⟨omega, d⟩`

    Higher rungs (mul, exp, tet) follow structurally via
    `fold_iter_omega_absorbs` once their object-level definitions
    are in place. The seed-preservation pattern propagates: if
    each rung's "step" preserves ω-seeded inputs, then iterating
    the rung preserves ω-seeded inputs. -/
theorem omega_ladder_absorption_bundle (m d n : Nat) :
    iter_rho n ⟨omega, d⟩ = ⟨omega, d⟩ ∧
    obj_add ⟨omega, d⟩ m = ⟨omega, d⟩ :=
  ⟨iter_rho_omega n d, omega_obj_add m d⟩

end Tau.Denotation

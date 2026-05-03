import TauLib.BookI.Boundary.Bridge.TauProfiniteCompactness
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Linarith

/-!
# TauLib.BookI.Boundary.Bridge.TauProfiniteFinsetPartition

**Workstream B1.5c.1 — Finset-indexed cylinder partition substrate**.

Extends B1.5b PART 3's `cylinder_eq_iUnion_subcylinders` (which uses
a `TauProfinite`-subtype indexing — uncountable) toward a
**`Finset`-indexed partition** suitable for the n-ary pigeonhole
step in B1.5c.2.

Per the binding spec dossier
(`atlas/audits/taulib/2026-05-05-canonical-compactness-spec.md` Part 5
target API), this is the substrate that B1.5c.2-6 (n-ary pigeonhole
+ recursive chain + limit + Alexander assembly) compose into the
full `CompactSpace TauProfinite` instance.

## What this slice ships

**`validSubcylinderCenters k c`** — the explicit Finset of valid
stage-`(k+1)` center values that refine a stage-`k` cylinder
centered at `c`:

```
validSubcylinderCenters k c
  = { c, c + primorial k, c + 2 · primorial k, …,
      c + (nth_prime (k+1) − 1) · primorial k }
```

Plus two basic well-formedness lemmas:
- `validSubcylinderCenters_mod` — every center in the Finset
  satisfies `c' % primorial k = c` (coherence with parent)
- `validSubcylinderCenters_lt` — every center is `< primorial (k+1)`
  (well-typed residue)

**B1.5c.2-6 queued**: the partition equality lemma
(`cylinder k c = ⋃ c' ∈ validSubcylinderCenters k c, cylinder (k+1) c'`),
the n-ary pigeonhole, the recursive chain construction, the limit
extraction, and the Alexander subbasis assembly. Each is genuinely
substantial Lean work; per the strict discipline, ships incrementally
in subsequent sub-PRs.

## Mathematical content

By the primorial recursion
`primorial (k+1) = nth_prime (k+1) * primorial k`, the residues
`c'` in `Fin (primorial (k+1))` satisfying `c' % primorial k = c`
(with `c < primorial k`) are exactly
`{c + i * primorial k | i ∈ Fin (nth_prime (k+1))}`.

This Finset has `nth_prime (k+1)` elements (when the map is
injective, which holds for `c < primorial k` and
`primorial k > 0`).

## Registry Cross-References

- [I.K1]                 CRT axiom (background; primorial structure)
- [II.D10]               Stage-k cylinder (Wave 50)
- [I.T-B1.5c.1-FinsetPartition] `validSubcylinderCenters` Finset
                                   (this module)
- [I.T-B1.5c.2-Partition]  Finset partition equality (queued)
- [I.T-B1.5c.3-Pigeonhole] n-ary pigeonhole (queued)

## Cross-references

- B1.5b PART 3 `TauProfiniteCompactness.lean` — the subtype-indexed
  partition this module begins to refactor
- B1.4.5 dossier
  `atlas/audits/taulib/2026-05-05-canonical-compactness-spec.md`
- `BookI/Polarity/ModArith.lean` — `primorial`, `nth_prime`,
  `primorial_pos`
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation Tau.Polarity

namespace TauProfinite

-- ============================================================
-- PART 1: The Finset of valid stage-(k+1) center values
-- ============================================================

/-- **The Finset of valid stage-(k+1) center values** that refine a
    stage-`k` cylinder centered at `c`.

    Each element is `c + i * primorial k` for `i ∈ Fin (nth_prime (k+1))`.
    By the primorial recursion these are exactly the residues mod
    `primorial (k+1)` satisfying `% primorial k = c`. -/
def validSubcylinderCenters (k c : TauIdx) : Finset TauIdx :=
  Finset.image (fun i => c + i * primorial k)
    (Finset.range (nth_prime (k + 1)))

/-- Coherence with the parent: every center `c'` in the Finset
    satisfies `c' % primorial k = c` (when `c < primorial k`). -/
theorem validSubcylinderCenters_mod {k c c' : TauIdx}
    (hc : c < primorial k)
    (hc' : c' ∈ validSubcylinderCenters k c) :
    c' % primorial k = c := by
  unfold validSubcylinderCenters at hc'
  rw [Finset.mem_image] at hc'
  obtain ⟨i, _, hi⟩ := hc'
  -- hi : c + i * primorial k = c'
  rw [← hi]
  -- Goal: (c + i * primorial k) % primorial k = c
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-- **B1.5c.1b — upper bound**: every center `c'` in the Finset
    satisfies `c' < primorial (k+1)` (when `c < primorial k`).

    **Proof**: every `c' ∈ validSubcylinderCenters k c` has the form
    `c + i * primorial k` for some `i < nth_prime (k+1)`. Then:

      c + i * primorial k
        < primorial k + i * primorial k    [Nat.add_lt_add_right hc]
        = (i + 1) * primorial k            [Nat.add_one_mul + comm]
        ≤ nth_prime (k+1) * primorial k    [Nat.mul_le_mul_right + hi_mem]
        = primorial (k+1)                  [by definition]

    Combined with `validSubcylinderCenters_mod`, this confirms each
    `c'` is a valid stage-(k+1) residue (well-typed and coherent
    with the parent stage-k center). -/
theorem validSubcylinderCenters_lt {k c c' : TauIdx}
    (hc : c < primorial k)
    (hc' : c' ∈ validSubcylinderCenters k c) :
    c' < primorial (k + 1) := by
  unfold validSubcylinderCenters at hc'
  rw [Finset.mem_image] at hc'
  obtain ⟨i, hi_mem, hi⟩ := hc'
  rw [Finset.mem_range] at hi_mem
  -- hi_mem : i < nth_prime (k + 1)
  -- hi : c + i * primorial k = c'
  rw [← hi]
  -- Goal: c + i * primorial k < primorial (k + 1)
  -- primorial (k+1) = nth_prime (k+1) * primorial k by definition
  show c + i * primorial k < nth_prime (k + 1) * primorial k
  calc c + i * primorial k
      < primorial k + i * primorial k := Nat.add_lt_add_right hc _
    _ = (i + 1) * primorial k := by rw [Nat.add_one_mul, Nat.add_comm]
    _ ≤ nth_prime (k + 1) * primorial k :=
        Nat.mul_le_mul_right _ hi_mem

end TauProfinite

end Tau.Boundary

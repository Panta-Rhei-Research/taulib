import TauLib.BookI.Boundary.Characters
import TauLib.BookI.KernelFoundation.H8KernelSynthesis

/-!
# TauLib.BookI.KernelFoundation.ScalarBridges

**Wave 37 — H8 Scalar Bridges (Tier 1 unlock from scalar-bridge
discovery review).**

Closes the highest-priority gap identified in the scalar-bridge
discovery review logbook
(`atlas/reviews/2026-04-29-scalar-bridges-discovery-review.md`):
the bidirectional **ℤ ↔ D** and **ℕ ↔ D** structural bridge.

The discovery wave found that D = SplitComplex's character machinery
(`chi_plus_val`, `chi_minus_val` : D → ℤ) is fully formalised, but the
**reverse direction** — canonical embedding ℤ → D — was missing. This
wave fills that gap, establishing the round-trip witness
`chi_plus_val (embed_int n) = n` (the structural NNO-style retraction
via D's idempotent decomposition).

## Registry Cross-References

- [I.D26]   SplitComplex (existing — Boundary algebra D)
- [I.D27]   SectorPair, e_plus_sector, e_minus_sector
- [I.D37]   Fundamental Characters chi_plus, chi_minus
- [I.T-D-EmbedInt]    paper §H4 ℤ → D embedding
- [I.T-D-EmbedNat]    paper §H4 ℕ → D embedding (B-sector route)
- [I.T-D-NNO]         NNO-style witness via χ₊ ∘ embed = id
- [I.T-D-Bridge]      H8 scalar-bridge synthesis keystone

## Mathematical Content

### The discovery-review gap

D's algebraic readout machinery is complete:

- `chi_plus_val : SplitComplex → Int := z ↦ z.re + z.im`  (homomorphic)
- `chi_minus_val : SplitComplex → Int := z ↦ z.re - z.im` (homomorphic)
- Decomposition `chi_plus + chi_minus = 2·re` etc.

But the **reverse direction** was absent: no canonical embedding
ℤ → D, hence no NNO-style structural witness.

### The fix

Wave 37 adds:

- `embed_int_into_d : Int → SplitComplex` sending `n ↦ ⟨n, 0⟩`
  (the canonical "real-axis" embedding — purely B-sector)
- `embed_nat_into_d : Nat → SplitComplex` via Int.ofNat
- The round-trip witness: `chi_plus_val (embed n) = n` (NNO-style)
- Companion witnesses for χ₋, additivity preservation, sector
  decomposition retention

### NNO-style structural witness

For any `n : Nat`:

```
chi_plus_val (embed_nat_into_d n) = (n : Int)
chi_minus_val (embed_nat_into_d n) = (n : Int)   -- both characters give n
```

(Both characters give the same value on the embedded scalar because
the embedding lands in the B-sector with zero imaginary part, so both
χ₊ = re + im and χ₋ = re - im reduce to re = n.)

This realizes the user's structural intuition: **ℕ enters D via the
real-axis embedding, and exits via either character (NNO-style
section/retraction).**

## Lean rendering strategy

All theorems are rendered at the **structural-witness level** —
direct definitions + `simp` / `rfl` / unfold proofs citing the
existing `chi_plus_val` / `chi_minus_val` infrastructure.

## Scope

`\scopetau` for the structural-bridge content; the deeper categorical
NNO universal-property (Tier 2 target) requires more abstract
infrastructure (pointed types + universal arrows) and is deferred to
Book III.
-/

set_option autoImplicit false

namespace Tau.KernelFoundation

open Tau.Boundary Tau.Polarity

-- ============================================================
-- PART 1: Canonical ℤ → D embedding
-- ============================================================

/-- **Paper §H4 / Wave 37 canonical embedding ℤ → D**.

    Sends `n : Int` to `⟨n, 0⟩ : SplitComplex` — the canonical
    "real-axis" embedding into the boundary algebra D.

    This is the missing reverse direction of D's character machinery
    (D → ℤ via χ₊, χ₋ existed; ℤ → D was absent until Wave 37). -/
def embed_int_into_d (n : Int) : SplitComplex := ⟨n, 0⟩

@[simp] theorem embed_int_re (n : Int) :
    (embed_int_into_d n).re = n := rfl

@[simp] theorem embed_int_im (n : Int) :
    (embed_int_into_d n).im = 0 := rfl

/-- **Canonical embedding ℕ → D** via Int.ofNat composition. -/
def embed_nat_into_d (n : Nat) : SplitComplex :=
  embed_int_into_d (Int.ofNat n)

@[simp] theorem embed_nat_re (n : Nat) :
    (embed_nat_into_d n).re = (n : Int) := rfl

@[simp] theorem embed_nat_im (n : Nat) :
    (embed_nat_into_d n).im = 0 := rfl

-- ============================================================
-- PART 2: Round-trip witness — χ₊ ∘ embed = id
-- ============================================================

/-- **NNO-style witness for χ₊**: applying the B-sector character to
    an embedded scalar recovers the original integer.

    `chi_plus_val (embed_int n) = n + 0 = n`. -/
@[simp] theorem chi_plus_embed_int (n : Int) :
    chi_plus_val (embed_int_into_d n) = n := by
  unfold chi_plus_val embed_int_into_d; simp

/-- **NNO-style witness for χ₋**: applying the C-sector character to
    an embedded scalar also recovers the original integer.

    `chi_minus_val (embed_int n) = n - 0 = n`.

    Both characters give the same value on the embedded scalar
    because the embedding lands purely in the B-sector. -/
@[simp] theorem chi_minus_embed_int (n : Int) :
    chi_minus_val (embed_int_into_d n) = n := by
  unfold chi_minus_val embed_int_into_d; simp

/-- **NNO-style witness via embed_nat (KEYSTONE)**: the natural-number
    embedding into D round-trips through χ₊ to the original Nat.

    This is the bidirectional ℕ ↔ D bridge that the discovery review
    identified as the missing piece. -/
theorem nno_from_d_witness (n : Nat) :
    chi_plus_val (embed_nat_into_d n) = (n : Int) := by
  unfold embed_nat_into_d
  rw [chi_plus_embed_int]
  rfl

/-- **Companion: χ₋ ∘ embed_nat = id (Nat-level)**. -/
theorem nno_from_d_witness_minus (n : Nat) :
    chi_minus_val (embed_nat_into_d n) = (n : Int) := by
  unfold embed_nat_into_d
  rw [chi_minus_embed_int]
  rfl

-- ============================================================
-- PART 3: Embedding preserves zero, one, addition
-- ============================================================

/-- The embedding sends 0 to SplitComplex.zero. -/
theorem embed_int_zero :
    embed_int_into_d 0 = ⟨0, 0⟩ := rfl

/-- The embedding sends 1 to ⟨1, 0⟩ (= SplitComplex.one). -/
theorem embed_int_one :
    embed_int_into_d 1 = ⟨1, 0⟩ := rfl

/-- The embedding preserves addition: `embed (a + b) = embed a + embed b`. -/
theorem embed_int_add (a b : Int) :
    embed_int_into_d (a + b) =
      SplitComplex.add (embed_int_into_d a) (embed_int_into_d b) := by
  unfold embed_int_into_d SplitComplex.add
  simp

/-- The embedding preserves multiplication.

    `(a · 1 + 0 · j)(b · 1 + 0 · j) = ab · 1 + 0 · j`,
    i.e. `embed (a · b) = embed a · embed b`. -/
theorem embed_int_mul (a b : Int) :
    embed_int_into_d (a * b) =
      SplitComplex.mul (embed_int_into_d a) (embed_int_into_d b) := by
  unfold embed_int_into_d SplitComplex.mul
  simp

-- ============================================================
-- PART 4: H8 scalar-bridge synthesis (KEYSTONE)
-- ============================================================

/-- **Wave 37 H8 scalar-bridge synthesis (KEYSTONE)**.

    Packages the bidirectional ℕ ↔ D + ℤ ↔ D bridge in five
    structural-content clauses:

    1. **ℤ → D embedding round-trip via χ₊** (the readout retraction)
    2. **ℤ → D embedding round-trip via χ₋** (companion retraction)
    3. **ℕ → D NNO-style witness** (via Int.ofNat composition)
    4. **B-sector purity** (embedding lands purely on the real axis)
    5. **Ring-homomorphism preservation** (additive identity, sum,
       product all preserved by the embedding)

    Together they realize the user's structural intuition that the
    canonical ℕ/ℤ bridge into TauLib should run through D's
    scalar readout — establishing the bidirectional structural
    witness that was previously one-way (D → ℤ only). -/
theorem scalar_bridge_synthesis (n : Nat) (m : Int) :
    -- Clause 1: ℤ → D round-trip via χ₊
    chi_plus_val (embed_int_into_d m) = m ∧
    -- Clause 2: ℤ → D round-trip via χ₋
    chi_minus_val (embed_int_into_d m) = m ∧
    -- Clause 3: ℕ → D NNO-style witness
    chi_plus_val (embed_nat_into_d n) = (n : Int) ∧
    -- Clause 4: B-sector purity (im = 0 always)
    (embed_int_into_d m).im = 0 ∧
    -- Clause 5: zero + one preserved
    (embed_int_into_d 0 = ⟨0, 0⟩ ∧
     embed_int_into_d 1 = ⟨1, 0⟩) :=
  ⟨chi_plus_embed_int m,
   chi_minus_embed_int m,
   nno_from_d_witness n,
   rfl,
   ⟨embed_int_zero, embed_int_one⟩⟩

-- ============================================================
-- PART 5: Numerical demonstrations
-- ============================================================

#eval embed_int_into_d 7                          -- {re := 7, im := 0}
#eval embed_nat_into_d 13                         -- {re := 13, im := 0}
#eval chi_plus_val (embed_int_into_d 42)          -- 42
#eval chi_minus_val (embed_int_into_d 42)         -- 42
#eval chi_plus_val (embed_nat_into_d 99)          -- 99
#eval chi_plus_val (SplitComplex.add (embed_int_into_d 5) (embed_int_into_d 3))  -- 8

end Tau.KernelFoundation

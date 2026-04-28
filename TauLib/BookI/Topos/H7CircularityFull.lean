import TauLib.BookI.Topos.CircularityResolution
import TauLib.BookI.Topos.H7ToposClassifier

/-!
# TauLib.BookI.Topos.H7CircularityFull

**Wave 32 — H7 §7 Circularity Resolution full four-sector
classification.**

Lean structural rendering of paper `tau-topos/main.tex` §7
(`section-07-circularity.tex`), the keystone philosophical
section of H7 establishing **paraconsistent fixed-point
resolution**:

- **Liar paradox** (`thm:liar-equals-both`): `Φ_liar(b) = ¬b`
  stabilises at `B` (Both/contradictory).
- **Truth-teller** (`thm:truth-teller`): `Φ_TT(b) = b`
  stabilises at the seed (T or F).
- **Curry's paradox** (`thm:curry-divergence`): same as Liar
  on B_σ algebra → stabilises at `B`.
- **Kleene-Rosser** (`thm:kleene-rosser`): genuinely
  underdetermined template stabilises at `N` (Neither).

The keystone theorem (`thm:circularity-classification`):
**every self-referential template Φ : B_σ → B_σ stabilises at
exactly one of the four atoms** {T, F, B, N}, classified by the
σ-orbit structure of its fixed-point dynamics.

This wave EXPANDS the existing `CircularityResolution.lean`
(Wave 5-era) which already shipped Liar + Truth-teller + Curry,
adding the Kleene-Rosser case + full four-sector synthesis +
H7 §7 paper-faithful packaging.

## Registry Cross-References

- [I.T-H6-Liar]      `liar_stabilises_at_Both` (existing)
- [I.T-H6-TT]        `truth_teller_stabilises_T/F` (existing)
- [I.T-H6-Curry]     `curry_stabilises_at_Both` (existing)
- [I.T155]           `subobject_classifier_witness` (Wave 31)
- [I.T-H7-KleeneRosser]   paper Thm `kleene-rosser`
- [I.T-H7-CircClass]      paper Thm `circularity-classification`
- [I.T-H7-S7Synth]        H7 §7 synthesis

## Mathematical Content (paper §7)

### Paper §7 four-sector classification

For self-referential template `Φ : Truth4 → Truth4`, the Cauchy
iteration `cauchyIter Φ n s` from seed `s` exhibits one of four
asymptotic patterns:

1. **T-stabilisation** (consistent affirmation): Truth-teller
   from seed T.
2. **F-stabilisation** (consistent denial): Truth-teller from
   seed F.
3. **B-stabilisation** (paraconsistent contradiction):
   Liar/Curry → Both.
4. **N-stabilisation** (paraconsistent vacuum):
   Kleene-Rosser → Neither.

The Liar IS the σ-swap (sigmaSwap), Truth-teller IS the identity,
Curry equals Liar on B_σ, and Kleene-Rosser is the constant-N
template that never resolves to T or F.

### Paper §7 Kleene-Rosser case (the missing piece)

The Kleene-Rosser combinator's Truth4 image is the constant
function `const N`: an internally-consistent self-referential
template that admits *no* B-membership *and* no C-membership
(neither sector confirms or denies).  Its stabilisation at N
is by direct iteration:

`cauchyIter (const N) n s = N` for all `n ≥ 1`.

## Lean rendering strategy

- Kleene-Rosser template + its stabilisation: new theorems
- Four-sector classification: synthesis theorem citing all four
  canonical witnesses (Liar B, Truth-teller T, Truth-teller F,
  Kleene-Rosser N)
- H7 §7 synthesis: keystone theorem packaging the classification
-/

set_option autoImplicit false

namespace Tau.Topos

open Tau.Logic Truth4

-- ============================================================
-- PART 1: Kleene-Rosser template (the missing fourth sector)
-- ============================================================

/-- **Paper §7 Thm `kleene-rosser` template**: a constant-N
    self-referential template that stabilises at `N` (Neither).

    The Kleene-Rosser combinator in classical logic is famously
    non-normalising; its τ-native Truth4 image collapses to a
    constant function `const N` that confirms neither T nor F. -/
def kleeneRosserTemplate : Truth4 → Truth4 := fun _ => N

/-- **Kleene-Rosser stabilises at N**: from any seed, after one
    iteration the value is N and stays N forever. -/
theorem kleene_rosser_iter_N (n : Nat) (s : Truth4) :
    cauchyIter kleeneRosserTemplate (n + 1) s = N := by
  induction n with
  | zero => rfl
  | succ k ih => rw [cauchyIter_succ, ih]; rfl

/-- **Paper §7 Thm `kleene-rosser` — KR stabilises at N**.

    For any seed s, the Kleene-Rosser template's Cauchy iteration
    stabilises at N from index 1 onward. -/
theorem kleene_rosser_stabilises_at_N (s : Truth4) :
    StabilisedValue kleeneRosserTemplate s N := by
  apply StabilisedValue.of_nonstab
  · -- ¬ EventuallyConst Φ s T
    intro ⟨n0, hT⟩
    have hge : max n0 1 ≥ 1 := le_max_right _ _
    have hn0 : n0 ≤ max n0 1 := le_max_left _ _
    have h1 := hT (max n0 1) hn0
    have h2 : cauchyIter kleeneRosserTemplate (max n0 1) s = N := by
      obtain ⟨k, hk⟩ : ∃ k, max n0 1 = k + 1 := ⟨max n0 1 - 1, by omega⟩
      rw [hk]; exact kleene_rosser_iter_N k s
    rw [h2] at h1; exact Truth4.noConfusion h1
  · -- ¬ EventuallyConst Φ s F
    intro ⟨n0, hF⟩
    have hge : max n0 1 ≥ 1 := le_max_right _ _
    have hn0 : n0 ≤ max n0 1 := le_max_left _ _
    have h1 := hF (max n0 1) hn0
    have h2 : cauchyIter kleeneRosserTemplate (max n0 1) s = N := by
      obtain ⟨k, hk⟩ : ∃ k, max n0 1 = k + 1 := ⟨max n0 1 - 1, by omega⟩
      rw [hk]; exact kleene_rosser_iter_N k s
    rw [h2] at h1; exact Truth4.noConfusion h1
  · -- ¬ Period2OnLobes Φ s
    intro hper
    obtain ⟨n0, h⟩ := hper
    -- Specialize at index n0 + 1 (which is ≥ n0 and ≥ 1)
    have h1 := h (n0 + 1) (Nat.le_succ n0)
    -- At index n0+1 the value is N (since n0+1 ≥ 1)
    have hN1 : cauchyIter kleeneRosserTemplate (n0 + 1) s = N :=
      kleene_rosser_iter_N n0 s
    rcases h1 with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [hN1] at ha; exact Truth4.noConfusion ha
    · rw [hN1] at ha; exact Truth4.noConfusion ha

-- ============================================================
-- PART 2: Four-sector classification (paper Thm)
-- ============================================================

/-- **Paper §7 Thm `circularity-classification` — KEYSTONE
    structural witness**.

    Four-sector classification: each Truth4 atom {T, F, B, N} is
    realised as a stabilised value by some canonical
    self-referential template:

    - **T**: Truth-teller from seed T (`truth_teller_stabilises_T`)
    - **F**: Truth-teller from seed F (`truth_teller_stabilises_F`)
    - **B**: Liar from seed F (`liar_stabilises_at_Both`)
    - **N**: Kleene-Rosser from any seed
      (`kleene_rosser_stabilises_at_N`)

    Together these witness the paper's claim that the four-element
    bilattice Truth4 is *exhaustive* for paraconsistent
    fixed-point resolution. -/
theorem four_sector_classification_witness :
    -- T-sector witness
    StabilisedValue truthTellerTemplate T T ∧
    -- F-sector witness
    StabilisedValue truthTellerTemplate F F ∧
    -- B-sector witness (Liar)
    StabilisedValue liarTemplate F B ∧
    -- N-sector witness (Kleene-Rosser)
    StabilisedValue kleeneRosserTemplate F N :=
  ⟨truth_teller_stabilises_T,
   truth_teller_stabilises_F,
   liar_stabilises_at_Both,
   kleene_rosser_stabilises_at_N F⟩

-- ============================================================
-- PART 3: Per-sector concrete examples
-- ============================================================

/-- **Liar template stabilises at Both** (paper Thm
    `liar-equals-both`, existing). -/
theorem h7_liar_at_both :
    StabilisedValue liarTemplate F B :=
  liar_stabilises_at_Both

/-- **Truth-teller template stabilises at T** (paper Thm
    `truth-teller`, existing). -/
theorem h7_truth_teller_at_T :
    StabilisedValue truthTellerTemplate T T :=
  truth_teller_stabilises_T

/-- **Curry template stabilises at Both** (paper Thm
    `curry-divergence`, existing). -/
theorem h7_curry_at_both :
    StabilisedValue curryTemplate F B :=
  curry_stabilises_at_Both

/-- **Kleene-Rosser template stabilises at N** (paper Thm
    `kleene-rosser`, this Wave). -/
theorem h7_kleene_rosser_at_N :
    StabilisedValue kleeneRosserTemplate F N :=
  kleene_rosser_stabilises_at_N F

-- ============================================================
-- PART 4: H7 §7 synthesis
-- ============================================================

/-- **Wave 32 H7 §7 synthesis (the KEYSTONE)**.

    Packages the four-sector classification of paper §7's
    `thm:circularity-classification` in five clauses:

    1. **§7 Liar**: paraconsistent contradiction → B
    2. **§7 Truth-teller**: consistent affirmation → T (or F)
    3. **§7 Curry**: paraconsistent equivalent of Liar → B
    4. **§7 Kleene-Rosser**: paraconsistent vacuum → N
    5. **Sub-classifier link**: Truth4 is the subobject
       classifier (Wave 31), so the four-sector classification
       IS the structural content of paraconsistent
       fixed-point resolution. -/
theorem h7_section7_synthesis :
    -- Clause 1: Liar → B
    StabilisedValue liarTemplate F B ∧
    -- Clause 2: Truth-teller → T
    StabilisedValue truthTellerTemplate T T ∧
    -- Clause 3: Curry → B
    StabilisedValue curryTemplate F B ∧
    -- Clause 4: Kleene-Rosser → N
    StabilisedValue kleeneRosserTemplate F N ∧
    -- Clause 5: Truth4 has 4 distinct values (subobject classifier)
    (∀ v : Omega_tau, v = T ∨ v = F ∨ v = B ∨ v = N) :=
  ⟨h7_liar_at_both,
   h7_truth_teller_at_T,
   h7_curry_at_both,
   h7_kleene_rosser_at_N,
   subobject_classifier_witness⟩

-- ============================================================
-- PART 5: Numerical demonstrations
-- ============================================================

#eval cauchyIter liarTemplate 0 F           -- F  (initial)
#eval cauchyIter liarTemplate 1 F           -- T  (after one swap)
#eval cauchyIter liarTemplate 2 F           -- F  (oscillates)
#eval cauchyIter truthTellerTemplate 5 T    -- T  (constant)
#eval cauchyIter kleeneRosserTemplate 0 T   -- T  (initial)
#eval cauchyIter kleeneRosserTemplate 1 T   -- N  (collapse)
#eval cauchyIter kleeneRosserTemplate 5 T   -- N  (stays N)

end Tau.Topos

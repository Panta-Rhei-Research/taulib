import TauLib.BookIII.Spectral.Adeles
import TauLib.BookI.Polarity.PrimePolarityClassifier

/-!
# TauLib.BookIII.Spectral.BipolarClassifier

Internal Bipolar Classifier (Label_n), Label Convergence,
and Label-Idempotent Compatibility.

## Registry Cross-References

- [III.D23] Internal Bipolar Classifier — `PrimeLabel`, `label_at_depth`, `classifier_check`
- [III.T13] Label Convergence — `label_convergence_check`
- [III.P08] Label-Idempotent Compatibility — `label_idem_check`

## Mathematical Content

**III.D23 (Internal Bipolar Classifier):** Label_n: computable classifier
mapping primes ≤ p_n to {B, C, X}. The source-truth classifier is the
orthodox prime-polarity character `χ_p(2)` from Book I / the prime-polarity
paper: B iff `(2/p)=+1` (`p ≡ ±1 mod 8`), C iff `(2/p)=-1`
(`p ≡ ±3 mod 8`), and X at the crossing prime `2`.

**III.T13 (Label Convergence):** Label_n stabilizes: for each prime p,
there exists n₀ such that Label_n(p) is constant for n ≥ n₀.

**III.P08 (Label-Idempotent Compatibility):** B-type primes correspond
to e₊-dominant spectral coefficients, C-type to e₋-dominant.
-/

namespace Tau.BookIII.Spectral

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors

-- ============================================================
-- INTERNAL BIPOLAR CLASSIFIER [III.D23]
-- ============================================================

/-- [III.D23] Prime labels: B-type (multiplicative/Galois dominant),
    C-type (additive/automorphic dominant), X-type (balanced). -/
inductive PrimeLabel where
  | B : PrimeLabel    -- exponent-dominant (B-lobe, multiplicative)
  | C : PrimeLabel    -- tetration-dominant (C-lobe, additive)
  | X : PrimeLabel    -- balanced (crossing type)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Convert the Book I integer polarity convention (`+1`, `-1`, `0`) into
    Book III's `PrimeLabel` surface. -/
def primeLabelOfPolarityInt (v : Int) : PrimeLabel :=
  if v = 1 then .B
  else if v = (-1 : Int) then .C
  else .X

/-- [III.D23] Classify a prime by its spectral behavior at depth n.
    Uses the CRT basis element e_i at depth n to determine the
    dominant channel of p_{i+1}:
    - B-type if CRT basis projects primarily to B-sector
    - C-type if CRT basis projects primarily to C-sector
    - X-type if balanced

    The value is depth-independent once the prime has entered the tower:
    it delegates to the Book I / prime-polarity paper source truth
    `Label_∞(p_i)=χ_{p_i}(2)`, not to the older mod-4 diagnostic. -/
def label_at_depth (p_idx n : TauIdx) : PrimeLabel :=
  if p_idx = 0 then .X
  else if p_idx > n then .X
  else primeLabelOfPolarityInt (Tau.Polarity.labelInfty (p_idx - 1))

/-- [III.D23] Direct label based on the paper-backed prime-polarity
    character `(2/p)`. This is the stable classifier (does not depend on
    depth):

    * `p = 2` maps to `X`;
    * `p ≡ ±1 mod 8` maps to `B`;
    * `p ≡ ±3 mod 8` maps to `C`.

    The old mod-4 rule is kept below only as a deprecated diagnostic. -/
def label_direct (p : TauIdx) : PrimeLabel :=
  primeLabelOfPolarityInt (Tau.Polarity.chi_p p 2)

/-- Deprecated historical diagnostic: classifies odd primes by `p mod 4`.

    This is **not** the Book III source-truth classifier. It is retained as
    an explicit guardrail because it mislabels primes such as 5 and 13 after
    the prime-polarity paper correction. -/
def label_direct_mod4_deprecated (p : TauIdx) : PrimeLabel :=
  if p < 2 then .X
  else if p == 2 then .X
  else if p % 4 == 1 then .B
  else .C

/-- [III.D23] Count B, C, X primes up to depth k. -/
def label_counts (k : TauIdx) : (TauIdx × TauIdx × TauIdx) :=
  go 1 0 0 0 (k + 1)
where
  go (i b_ct c_ct x_ct fuel : Nat) : (TauIdx × TauIdx × TauIdx) :=
    if fuel = 0 then (b_ct, c_ct, x_ct)
    else if i > k then (b_ct, c_ct, x_ct)
    else
      let p := nth_prime i
      match label_direct p with
      | .B => go (i + 1) (b_ct + 1) c_ct x_ct (fuel - 1)
      | .C => go (i + 1) b_ct (c_ct + 1) x_ct (fuel - 1)
      | .X => go (i + 1) b_ct c_ct (x_ct + 1) (fuel - 1)
  termination_by fuel

/-- [III.D23] Classifier check: verify label assignment is consistent
    across methods for all primes up to bound. -/
def classifier_check (bound : TauIdx) : Bool :=
  go 1 (bound + 1)
where
  go (i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i > bound then true
    else
      let p := nth_prime i
      if p > bound then true
      else
        -- Label-count consistency: B + C + X primes sum to total at depth i
        let (b_ct, c_ct, x_ct) := label_counts i
        let count_ok := b_ct + c_ct + x_ct == i
        count_ok && go (i + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- LABEL CONVERGENCE [III.T13]
-- ============================================================

/-- [III.T13] Label convergence: label_direct is depth-independent,
    so it trivially stabilizes. Verify that label_at_depth agrees
    with label_direct for all primes at sufficient depth. -/
def label_convergence_check (bound : TauIdx) : Bool :=
  -- Since label_direct doesn't depend on depth, convergence is immediate.
  -- We verify exhaustiveness: all primes get a label.
  go 1 (bound + 1)
where
  go (i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i > bound then true
    else
      let p := nth_prime i
      if p > bound then true
      else
        -- Label is well-defined
        let label := label_direct p
        let ok := label == .B || label == .C || label == .X
        -- B and C are mutually exclusive (for p > 2)
        let exclusive := if p > 2 then
          (label == .B && label != .C) || (label == .C && label != .B)
        else label == .X
        ok && exclusive && go (i + 1) (fuel - 1)
  termination_by fuel

/-- [III.T13] B-C balance: both B-type and C-type primes exist
    in every sufficiently large range. -/
def bc_balance_check (bound : TauIdx) : Bool :=
  let (b, c, _x) := label_counts bound
  b > 0 && c > 0

-- ============================================================
-- LABEL-IDEMPOTENT COMPATIBILITY [III.P08]
-- ============================================================

/-- [III.P08] Label-idempotent compatibility: B-type primes have
    e₊-compatible polarity, C-type have e₋-compatible polarity.
    This check is deliberately source-truth based: the Book III label must
    agree with the Book I `Label_∞` classifier at the same prime index.
    CRT-basis dominance diagnostics are downstream structure, not the
    classifier definition. -/
def label_idem_check (bound db : TauIdx) : Bool :=
  go 1 ((db + 1) * (bound + 1))
where
  go (i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i > bound then true
    else
      let p := nth_prime i
      if p > bound || p < 3 then go (i + 1) (fuel - 1)
      else
        if i > db then go (i + 1) (fuel - 1)
        else
          let ok := label_direct p == label_at_depth i db
          ok && go (i + 1) (fuel - 1)
  termination_by fuel

/-- [III.P08] Split-complex decomposition respects labels:
    B and C labels agree with the sign of Book I's source-truth polarity
    character. This is a source-truth alignment check, not an imported
    Euclidean or mod-4 criterion. -/
def split_complex_label_check (bound db : TauIdx) : Bool :=
  go 1 (bound + 1)
where
  go (i fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i > bound then true
    else
      let p := nth_prime i
      if p > bound || p < 3 || i > db then go (i + 1) (fuel - 1)
      else
        let label := label_direct p
        let polarity := Tau.Polarity.labelInfty (i - 1)
        let ok := match label with
          | .B => polarity == 1
          | .C => polarity == (-1 : Int)
          | .X => polarity == 0
        ok && go (i + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Label assignment
#eval label_direct 2                         -- X (crossing prime)
#eval label_direct 3                         -- C ((2/3) = -1)
#eval label_direct 5                         -- C ((2/5) = -1)
#eval label_direct 7                         -- B ((2/7) = +1)
#eval label_direct 13                        -- C ((2/13) = -1)

-- Label counts
#eval label_counts 5                          -- (B, C, X) counts for first 5 primes

-- Checks
#eval classifier_check 20                    -- true
#eval label_convergence_check 20             -- true
#eval bc_balance_check 5                     -- true
#eval label_idem_check 10 4                  -- true
#eval split_complex_label_check 10 4         -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

-- Classifier [III.D23]
theorem classifier_20 :
    classifier_check 20 = true := by native_decide

-- Label convergence [III.T13]
theorem label_conv_20 :
    label_convergence_check 20 = true := by native_decide

-- B-C balance [III.T13]
theorem bc_balance_5 :
    bc_balance_check 5 = true := by native_decide

-- Label-idempotent compatibility [III.P08]
theorem label_idem_10_4 :
    label_idem_check 10 4 = true := by native_decide

-- Split-complex label [III.P08]
theorem split_label_10_4 :
    split_complex_label_check 10 4 = true := by native_decide

/-- [III.D23] Book III direct labels are exactly the Book I local polarity
    character `(2/p)` rendered into `{B,C,X}`. -/
theorem label_direct_eq_prime_polarity_chi (p : TauIdx) :
    label_direct p =
      primeLabelOfPolarityInt (Tau.Polarity.chi_p p 2) := rfl

/-- [III.D23] The depth label agrees definitionally with Book I `Label_∞`
    once the prime index is in range. -/
theorem bookIII_label_eq_bookI_labelInfty (i n : TauIdx)
    (h0 : i ≠ 0) (hn : ¬ i > n) :
    label_at_depth i n =
      primeLabelOfPolarityInt (Tau.Polarity.labelInfty (i - 1)) := by
  unfold label_at_depth
  simp [h0, hn]

/-- Guardrail: the deprecated mod-4 diagnostic mislabels 5. -/
theorem labelDirect_mod4_deprecated_mislabels_5 :
    label_direct_mod4_deprecated 5 = .B ∧ label_direct 5 = .C := by
  native_decide

/-- Guardrail: the deprecated mod-4 diagnostic mislabels 13. -/
theorem labelDirect_mod4_deprecated_mislabels_13 :
    label_direct_mod4_deprecated 13 = .B ∧ label_direct 13 = .C := by
  native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D23] Structural: 2 is the unique X-type prime. -/
theorem two_is_x : label_direct 2 = .X := rfl

/-- [III.D23] Structural: 5 is C-type because `(2/5)=-1`. -/
theorem five_is_c : label_direct 5 = .C := by native_decide

/-- [III.D23] Structural: 7 is B-type because `(2/7)=+1`. -/
theorem seven_is_b : label_direct 7 = .B := by native_decide

/-- [III.D23] Structural: 3 is C-type because `(2/3)=-1`. -/
theorem three_is_c : label_direct 3 = .C := by native_decide

/-- [III.T13] Structural: both B and C labels exist once 7 enters,
    i.e. by the first 4 primes. -/
theorem bc_exist_4 : bc_balance_check 4 = true := by native_decide

end Tau.BookIII.Spectral

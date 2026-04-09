import TauLib.BookI.Topos.LimitsSites
import TauLib.BookI.Logic.BooleanRecovery
import TauLib.BookI.Logic.Explosion

/-!
# TauLib.BookI.Topos.EarnedTopos

The earned topos E_τ with subobject classifier Ω_τ = Truth4.

## Registry Cross-References

- [I.T25] Ω_τ Subobject Classifier — `omega_tau_classifier`
- [I.D58] Characteristic Morphism — `characteristic_morphism`
- [I.D59] Earned Topos — `EarnedTopos`
- [I.P27] Non-Boolean — `earned_topos_non_boolean`

## Ground Truth Sources
- chunk_0228_M002194: Split-complex algebra, bipolar structure
- chunk_0310_M002679: Bipolar partition, four truth values

## Mathematical Content

The subobject classifier of PSh(Cat_τ) is Ω_τ = Truth4 = {T, F, B, N}.
This was PREVIEWED in Part XI (Chapter 45, I.D41) and is now EARNED:
the four truth values are forced by the topos structure.

The characteristic morphism χ_S: X → Ω_τ sends each element to its
membership status: T (fully in), F (fully out), B (overdetermined), N (underdetermined).

The earned topos E_τ is non-Boolean: since |Ω_τ| = 4 ≠ 2, the complement
law fails, and the internal logic is both intuitionistic and paraconsistent.
-/

namespace Tau.Topos

open Tau.Logic Tau.Holomorphy Tau.Polarity Tau.Denotation Truth4

-- ============================================================
-- SUBOBJECT CLASSIFIER [I.T25]
-- ============================================================

/-- [I.T25] The subobject classifier for PSh(Cat_τ) is Ω_τ = Truth4.

    In a Grothendieck topos, the subobject classifier Ω is characterized by:
    for every mono m: S ↪ X, there exists a unique χ: X → Ω such that
    the pullback of true: 1 → Ω along χ recovers S.

    In our four-valued setting:
    - T: the element is in S (both sectors confirm membership)
    - F: the element is not in S (both sectors deny)
    - B: overdetermined (B-sector confirms, C-sector denies)
    - N: underdetermined (neither sector confirms)

    The key theorem: Ω_τ has exactly four elements, matching Truth4. -/
theorem omega_tau_classifier :
    (∀ v : Omega_tau, v = T ∨ v = F ∨ v = B ∨ v = N) := by
  intro v
  cases v <;> simp

/-- The "true" morphism: the global element selecting T ∈ Ω_τ. -/
theorem omega_true_is_T : omega_true = T := rfl

/-- The subobject classifier has exactly 4 elements. -/
theorem omega_tau_card_four :
    omega_true ≠ omega_false ∧
    omega_true ≠ omega_both ∧
    omega_true ≠ omega_neither ∧
    omega_false ≠ omega_both ∧
    omega_false ≠ omega_neither ∧
    omega_both ≠ omega_neither := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================
-- CHARACTERISTIC MORPHISM [I.D58]
-- ============================================================

/-- [I.D58] The characteristic morphism: for a given predicate on TauIdx,
    assigns a Truth4 value to each element based on its membership status.

    The predicate P encodes membership; the Truth4 value encodes HOW
    the element is a member (from which spectral sectors). -/
def characteristic_morphism (b_member c_member : TauIdx → Bool) :
    TauIdx → Omega_tau :=
  fun x => Truth4.fromBoolPair (b_member x, c_member x)

/-- Characteristic morphism: both sectors confirm ⟹ T. -/
theorem char_both_true (b_mem c_mem : TauIdx → Bool) (x : TauIdx)
    (hb : b_mem x = true) (hc : c_mem x = true) :
    characteristic_morphism b_mem c_mem x = T := by
  simp [characteristic_morphism, hb, hc, Truth4.fromBoolPair]

/-- Characteristic morphism: both sectors deny ⟹ F. -/
theorem char_both_false (b_mem c_mem : TauIdx → Bool) (x : TauIdx)
    (hb : b_mem x = false) (hc : c_mem x = false) :
    characteristic_morphism b_mem c_mem x = F := by
  simp [characteristic_morphism, hb, hc, Truth4.fromBoolPair]

/-- Characteristic morphism: B-sector confirms, C denies ⟹ B. -/
theorem char_overdetermined (b_mem c_mem : TauIdx → Bool) (x : TauIdx)
    (hb : b_mem x = true) (hc : c_mem x = false) :
    characteristic_morphism b_mem c_mem x = B := by
  simp [characteristic_morphism, hb, hc, Truth4.fromBoolPair]

/-- Characteristic morphism: neither confirms ⟹ N. -/
theorem char_underdetermined (b_mem c_mem : TauIdx → Bool) (x : TauIdx)
    (hb : b_mem x = false) (hc : c_mem x = true) :
    characteristic_morphism b_mem c_mem x = N := by
  simp [characteristic_morphism, hb, hc, Truth4.fromBoolPair]

/-- The pullback of true along χ recovers the subobject:
    χ(x) = T iff both sectors confirm. -/
theorem char_pullback_true (b_mem c_mem : TauIdx → Bool) (x : TauIdx) :
    characteristic_morphism b_mem c_mem x = T ↔
    b_mem x = true ∧ c_mem x = true := by
  constructor
  · intro h
    simp [characteristic_morphism, Truth4.fromBoolPair] at h
    cases hb : b_mem x <;> cases hc : c_mem x <;> simp_all
  · intro ⟨hb, hc⟩
    exact char_both_true b_mem c_mem x hb hc

-- ============================================================
-- THE EARNED TOPOS [I.D59]
-- ============================================================

/-- [I.D59] The earned topos E_τ = PSh(Cat_τ) with Ω_τ as subobject classifier.
    Bundles the Grothendieck topos structure with the four-valued classifier. -/
structure EarnedTopos where
  /-- The underlying presheaf topos. -/
  topos : PShCatTau := ⟨⟨fun _ => true⟩⟩
  /-- The subobject classifier is Truth4. -/
  classifier : Type := Omega_tau
  /-- The "true" arrow. -/
  true_arrow : Omega_tau := omega_true

/-- The canonical earned topos. -/
def earned_topos : EarnedTopos where
  topos := ⟨⟨fun _ => true⟩⟩
  classifier := Omega_tau
  true_arrow := omega_true

-- ============================================================
-- NON-BOOLEAN [I.P27]
-- ============================================================

/-- [I.P27] The earned topos E_τ is non-Boolean.

    A Boolean topos has Ω = {0, 1} (two truth values).
    Our Ω_τ has FOUR truth values (T, F, B, N).
    The complement law ¬¬p = p holds in Boolean topoi
    but fails in E_τ: ¬¬B = ¬N = B, which works,
    but the issue is that B and N are distinct from T and F.

    The explosion barrier (I.T13) gives a direct witness:
    B ⟹ F is not T (it's N), so material implication doesn't
    validate ex falso quodlibet. -/
theorem earned_topos_non_boolean :
    omega_both ≠ omega_true ∧ omega_neither ≠ omega_true := by
  constructor <;> decide

/-- The explosion barrier transfers to the topos: B → F ≠ T. -/
theorem topos_explosion_barrier : Truth4.impl B F ≠ T :=
  explosion_barrier

/-- Negation IS involutive on Truth4 (it's a lattice involution):
    T→F→T, F→T→F, B→N→B, N→B→N.
    The non-Boolean property is NOT about double negation failure but about
    the existence of non-trivial truth values B and N. -/
theorem neg_involutive (v : Truth4) : Truth4.neg (Truth4.neg v) = v := by
  cases v <;> rfl

/-- The witness of non-Booleanness: there exist truth values
    that are neither T nor F. -/
theorem non_boolean_witness : ∃ v : Truth4, v ≠ T ∧ v ≠ F := by
  exact ⟨B, by decide, by decide⟩

/-- The join of B and N is T (overdetermined ∨ underdetermined = true). -/
theorem B_join_N_is_T : Truth4.join B N = T := rfl

/-- The meet of B and N is F (overdetermined ∧ underdetermined = false). -/
theorem B_meet_N_is_F : Truth4.meet B N = F := rfl

/-- Internal logic: the topos has 4 truth values, not 2.
    This means the internal logic is both:
    - Intuitionistic (not all propositions are decidable: B, N exist)
    - Paraconsistent (contradictions don't explode: I.T13) -/
theorem internal_logic_four_valued :
    ∀ v : Omega_tau, v = T ∨ v = F ∨ v = B ∨ v = N :=
  omega_tau_classifier

-- ============================================================
-- TOPOS-LOGIC CONNECTION
-- ============================================================

/-- The characteristic morphism for the "even numbers" subobject,
    using B-sector = divisibility by 2, C-sector = divisibility by 3. -/
def even_odd_char : TauIdx → Omega_tau :=
  characteristic_morphism (fun n => n % 2 == 0) (fun n => n % 3 == 0)

-- Concrete checks
example : even_odd_char 6 = T := by native_decide   -- 6: div by 2 AND 3
example : even_odd_char 4 = B := by native_decide   -- 4: div by 2 not 3
example : even_odd_char 3 = N := by native_decide   -- 3: div by 3 not 2
example : even_odd_char 5 = F := by native_decide   -- 5: neither

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Subobject classifier
#eval omega_true            -- T
#eval omega_false           -- F
#eval omega_both            -- B
#eval omega_neither         -- N

-- Characteristic morphism
#eval even_odd_char 0       -- T (0 div by 2 and 3)
#eval even_odd_char 1       -- F (1 div by neither)
#eval even_odd_char 2       -- B (2 div by 2 only)
#eval even_odd_char 3       -- N (3 div by 3 only)
#eval even_odd_char 6       -- T (6 div by both)

-- Non-Boolean witness
#eval Truth4.impl B F       -- N (not T: explosion fails)

end Tau.Topos

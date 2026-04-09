import TauLib.BookI.Boundary.ConstructiveReals
import Mathlib.Tactic.Ring

/-!
# TauLib.BookI.Boundary.Quaternions

The elliptic quaternions: TauQuaternion = R_tau-algebra {1,i,j,k}.

## Registry Cross-References

- [I.D87] TauQuaternion — Elliptic quaternions over constructive reals
- [I.T44] Division Algebra — Hamilton product, i^2=j^2=k^2=ijk=-1
- [I.R22] Hurwitz — Only R, C, H, O are normed division algebras

## Ground Truth Sources
- Hamilton product structure: (a1+b1i+c1j+d1k)(a2+b2i+c2j+d2k)

## Mathematical Content

TauQuaternion is the 4-dimensional R_tau-algebra with basis {1,i,j,k}
satisfying i^2 = j^2 = k^2 = ijk = -1. This is a non-commutative
division algebra (the Hamilton quaternions over the constructive reals).

All operations are defined in terms of TauReal arithmetic. Equivalence
is componentwise TauReal.equiv. The key results are:
- i^2 = j^2 = k^2 = -1 (up to equiv)
- ijk = -1 (up to equiv)
- Non-commutativity: ij != ji
- Additive ring axioms (componentwise from TauReal)
- Multiplicative identity (one_mul, mul_one)
-/

set_option autoImplicit false

namespace Tau.Boundary

open Tau.Denotation

-- ============================================================
-- [I.D87] TauQuaternion: STRUCTURE
-- ============================================================

/-- [I.D87] TauQuaternion: elliptic quaternions over constructive reals.
    Components: w (scalar/real), x (i), y (j), z (k). -/
structure TauQuaternion where
  w : TauReal
  x : TauReal
  y : TauReal
  z : TauReal

-- ============================================================
-- EQUIVALENCE: COMPONENTWISE TauReal.equiv
-- ============================================================

/-- Two TauQuaternions are equivalent if all four components agree. -/
def TauQuaternion.equiv (a b : TauQuaternion) : Prop :=
  TauReal.equiv a.w b.w ∧ TauReal.equiv a.x b.x ∧
  TauReal.equiv a.y b.y ∧ TauReal.equiv a.z b.z

/-- TauQuaternion equivalence is reflexive. -/
theorem TauQuaternion.equiv_refl (a : TauQuaternion) : TauQuaternion.equiv a a :=
  ⟨TauReal.equiv_refl a.w, TauReal.equiv_refl a.x,
   TauReal.equiv_refl a.y, TauReal.equiv_refl a.z⟩

/-- TauQuaternion equivalence is symmetric. -/
theorem TauQuaternion.equiv_symm {a b : TauQuaternion} (h : TauQuaternion.equiv a b) :
    TauQuaternion.equiv b a :=
  ⟨TauReal.equiv_symm h.1, TauReal.equiv_symm h.2.1,
   TauReal.equiv_symm h.2.2.1, TauReal.equiv_symm h.2.2.2⟩

-- ============================================================
-- CONSTANTS: ZERO, ONE, BASIS ELEMENTS
-- ============================================================

/-- Quaternion zero: (0, 0, 0, 0). -/
def TauQuaternion.zero : TauQuaternion :=
  ⟨TauReal.zero, TauReal.zero, TauReal.zero, TauReal.zero⟩

/-- Quaternion one: (1, 0, 0, 0). -/
def TauQuaternion.one : TauQuaternion :=
  ⟨TauReal.one, TauReal.zero, TauReal.zero, TauReal.zero⟩

/-- Quaternion i: (0, 1, 0, 0). -/
def TauQuaternion.qi : TauQuaternion :=
  ⟨TauReal.zero, TauReal.one, TauReal.zero, TauReal.zero⟩

/-- Quaternion j: (0, 0, 1, 0). -/
def TauQuaternion.qj : TauQuaternion :=
  ⟨TauReal.zero, TauReal.zero, TauReal.one, TauReal.zero⟩

/-- Quaternion k: (0, 0, 0, 1). -/
def TauQuaternion.qk : TauQuaternion :=
  ⟨TauReal.zero, TauReal.zero, TauReal.zero, TauReal.one⟩

-- ============================================================
-- OPERATIONS: ADD, NEGATE, MUL, CONJ, NORMSQ
-- ============================================================

/-- Quaternion addition: componentwise. -/
def TauQuaternion.add (a b : TauQuaternion) : TauQuaternion :=
  ⟨a.w.add b.w, a.x.add b.x, a.y.add b.y, a.z.add b.z⟩

/-- Quaternion negation: componentwise. -/
def TauQuaternion.negate (a : TauQuaternion) : TauQuaternion :=
  ⟨a.w.negate, a.x.negate, a.y.negate, a.z.negate⟩

/-- Hamilton product:
    (a1 + b1i + c1j + d1k)(a2 + b2i + c2j + d2k) =
      (a1a2 - b1b2 - c1c2 - d1d2)
    + (a1b2 + b1a2 + c1d2 - d1c2)i
    + (a1c2 - b1d2 + c1a2 + d1b2)j
    + (a1d2 + b1c2 - c1b2 + d1a2)k -/
def TauQuaternion.mul (a b : TauQuaternion) : TauQuaternion :=
  ⟨((a.w.mul b.w).sub (a.x.mul b.x)).sub ((a.y.mul b.y).add (a.z.mul b.z)),
   ((a.w.mul b.x).add (a.x.mul b.w)).add ((a.y.mul b.z).sub (a.z.mul b.y)),
   ((a.w.mul b.y).sub (a.x.mul b.z)).add ((a.y.mul b.w).add (a.z.mul b.x)),
   ((a.w.mul b.z).add (a.x.mul b.y)).sub ((a.y.mul b.x).sub (a.z.mul b.w))⟩

/-- Quaternion conjugation: conj(a + bi + cj + dk) = a - bi - cj - dk. -/
def TauQuaternion.conj (a : TauQuaternion) : TauQuaternion :=
  ⟨a.w, a.x.negate, a.y.negate, a.z.negate⟩

/-- Quaternion norm squared: |a|^2 = w^2 + x^2 + y^2 + z^2. -/
def TauQuaternion.normSq (a : TauQuaternion) : TauReal :=
  ((a.w.mul a.w).add (a.x.mul a.x)).add ((a.y.mul a.y).add (a.z.mul a.z))

-- ============================================================
-- BRIDGE TACTIC: REDUCE TauReal EQUIV ON CONSTANTS TO TauRat
-- ============================================================

/-- Helper: TauReal component equivalence on constant sequences reduces
    to TauRat equivalence, which reduces to TauInt via the bridge. -/
private theorem taureal_const_bridge (a b : TauRat)
    (h : ∀ n : Nat, TauRat.equiv a b) : TauReal.equiv ⟨fun _ => a⟩ ⟨fun _ => b⟩ :=
  fun n => h n

-- ============================================================
-- [I.T44] HAMILTON RELATIONS: i^2 = j^2 = k^2 = ijk = -1
-- ============================================================

/-- The negation of one: (-1, 0, 0, 0). -/
def TauQuaternion.neg_one : TauQuaternion := TauQuaternion.negate TauQuaternion.one

/-- i^2 = -1: qi * qi is equivalent to negate one. -/
theorem qi_squared :
    TauQuaternion.equiv (TauQuaternion.mul TauQuaternion.qi TauQuaternion.qi)
                        TauQuaternion.neg_one := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n <;>
  simp only [TauQuaternion.mul, TauQuaternion.qi, TauQuaternion.neg_one,
    TauQuaternion.negate, TauQuaternion.one,
    TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
    TauReal.zero, TauReal.one,
    TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate,
    TauRat.zero, TauRat.one] <;>
  rw [equiv_iff_toInt_eq] <;>
  simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one] <;>
  push_cast <;> ring

/-- j^2 = -1: qj * qj is equivalent to negate one. -/
theorem qj_squared :
    TauQuaternion.equiv (TauQuaternion.mul TauQuaternion.qj TauQuaternion.qj)
                        TauQuaternion.neg_one := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n <;>
  simp only [TauQuaternion.mul, TauQuaternion.qj, TauQuaternion.neg_one,
    TauQuaternion.negate, TauQuaternion.one,
    TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
    TauReal.zero, TauReal.one,
    TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate,
    TauRat.zero, TauRat.one] <;>
  rw [equiv_iff_toInt_eq] <;>
  simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one] <;>
  push_cast <;> ring

/-- k^2 = -1: qk * qk is equivalent to negate one. -/
theorem qk_squared :
    TauQuaternion.equiv (TauQuaternion.mul TauQuaternion.qk TauQuaternion.qk)
                        TauQuaternion.neg_one := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n <;>
  simp only [TauQuaternion.mul, TauQuaternion.qk, TauQuaternion.neg_one,
    TauQuaternion.negate, TauQuaternion.one,
    TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
    TauReal.zero, TauReal.one,
    TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate,
    TauRat.zero, TauRat.one] <;>
  rw [equiv_iff_toInt_eq] <;>
  simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one] <;>
  push_cast <;> ring

/-- ijk = -1: qi * qj * qk is equivalent to negate one. -/
theorem ijk_relation :
    TauQuaternion.equiv
      (TauQuaternion.mul (TauQuaternion.mul TauQuaternion.qi TauQuaternion.qj) TauQuaternion.qk)
      TauQuaternion.neg_one := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n <;>
  simp only [TauQuaternion.mul, TauQuaternion.qi, TauQuaternion.qj, TauQuaternion.qk,
    TauQuaternion.neg_one, TauQuaternion.negate, TauQuaternion.one,
    TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
    TauReal.zero, TauReal.one,
    TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate,
    TauRat.zero, TauRat.one] <;>
  rw [equiv_iff_toInt_eq] <;>
  simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one] <;>
  push_cast <;> ring

-- ============================================================
-- NON-COMMUTATIVITY: ij != ji
-- ============================================================

/-- Non-commutativity witness: qi * qj and qj * qi differ in the z-component.
    qi * qj has z = 1 while qj * qi has z = -1. -/
theorem non_commutativity_witness :
    ¬ TauQuaternion.equiv (TauQuaternion.mul TauQuaternion.qi TauQuaternion.qj)
                          (TauQuaternion.mul TauQuaternion.qj TauQuaternion.qi) := by
  intro ⟨_, _, _, hz⟩
  -- hz : TauReal.equiv (z-component of qi*qj) (z-component of qj*qi)
  -- qi*qj has z = 1, qj*qi has z = -1
  have h0 := hz 0
  simp only [TauQuaternion.mul, TauQuaternion.qi, TauQuaternion.qj,
    TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
    TauReal.zero, TauReal.one,
    TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate,
    TauRat.zero, TauRat.one] at h0
  rw [equiv_iff_toInt_eq] at h0
  simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one] at h0
  omega

-- ============================================================
-- ADDITIVE RING AXIOMS (componentwise from TauReal)
-- ============================================================

/-- Quaternion addition is commutative (up to equiv). -/
theorem tauquat_add_comm (a b : TauQuaternion) :
    TauQuaternion.equiv (TauQuaternion.add a b) (TauQuaternion.add b a) :=
  ⟨taureal_add_comm a.w b.w, taureal_add_comm a.x b.x,
   taureal_add_comm a.y b.y, taureal_add_comm a.z b.z⟩

/-- Quaternion addition is associative (up to equiv). -/
theorem tauquat_add_assoc (a b c : TauQuaternion) :
    TauQuaternion.equiv ((TauQuaternion.add a b).add c)
                        (TauQuaternion.add a (TauQuaternion.add b c)) :=
  ⟨taureal_add_assoc a.w b.w c.w, taureal_add_assoc a.x b.x c.x,
   taureal_add_assoc a.y b.y c.y, taureal_add_assoc a.z b.z c.z⟩

/-- Quaternion zero is a right identity for addition (up to equiv). -/
theorem tauquat_add_zero (a : TauQuaternion) :
    TauQuaternion.equiv (a.add TauQuaternion.zero) a :=
  ⟨taureal_add_zero a.w, taureal_add_zero a.x,
   taureal_add_zero a.y, taureal_add_zero a.z⟩

/-- Quaternion negation is a right inverse for addition (up to equiv). -/
theorem tauquat_add_negate (a : TauQuaternion) :
    TauQuaternion.equiv (a.add a.negate) TauQuaternion.zero :=
  ⟨taureal_add_negate a.w, taureal_add_negate a.x,
   taureal_add_negate a.y, taureal_add_negate a.z⟩

-- ============================================================
-- MULTIPLICATIVE IDENTITY (but NOT mul_comm!)
-- ============================================================

/-- One is a right identity for quaternion multiplication (up to equiv). -/
theorem tauquat_mul_one (a : TauQuaternion) :
    TauQuaternion.equiv (TauQuaternion.mul a TauQuaternion.one) a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n <;>
  simp only [TauQuaternion.mul, TauQuaternion.one,
    TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
    TauReal.zero, TauReal.one,
    TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate,
    TauRat.zero, TauRat.one] <;>
  rw [equiv_iff_toInt_eq] <;>
  simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one] <;>
  push_cast <;> ring

/-- One is a left identity for quaternion multiplication (up to equiv). -/
theorem tauquat_one_mul (a : TauQuaternion) :
    TauQuaternion.equiv (TauQuaternion.mul TauQuaternion.one a) a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n <;>
  simp only [TauQuaternion.mul, TauQuaternion.one,
    TauReal.sub, TauReal.add, TauReal.mul, TauReal.negate,
    TauReal.zero, TauReal.one,
    TauRat.equiv, TauRat.sub, TauRat.add, TauRat.mul, TauRat.negate,
    TauRat.zero, TauRat.one] <;>
  rw [equiv_iff_toInt_eq] <;>
  simp only [toInt_add, toInt_mul, toInt_negate, toInt_fromNat, toInt_zero, toInt_one] <;>
  push_cast <;> ring

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#check TauQuaternion.mul TauQuaternion.qi TauQuaternion.qj
#check qi_squared
#check qj_squared
#check qk_squared
#check ijk_relation
#check non_commutativity_witness
#check tauquat_add_comm
#check tauquat_mul_one
#check tauquat_one_mul

end Tau.Boundary

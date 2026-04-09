import TauLib.BookI.Orbit.Generation

/-!
# TauLib.BookI.Orbit.Countability

Each orbit ray is countable (bijection with Nat), and Obj(τ) is countable.

## Registry Cross-References

- [I.P04] Orbit Countability — `orbit_countable`, `tauObj_countable`

## Mathematical Content

Each orbit ray O_g is in bijection with Nat via the map n ↦ ⟨g, n⟩.
The full universe Obj(τ) is countable: we construct an injection TauObj → Nat.
-/

namespace Tau.Orbit

open Tau.Kernel Generator

-- ============================================================
-- ORBIT RAY ENUMERATION
-- ============================================================

/-- Canonical enumeration of orbit ray O_g: n ↦ ⟨g, n⟩. -/
def orbitEnumerate (g : Generator) (_hg : g ≠ omega) (n : Nat) : TauObj :=
  ⟨g, n⟩

/-- [I.P04 part 1] Orbit enumeration is injective. -/
theorem orbit_enumerate_injective (g : Generator) (hg : g ≠ omega)
    (n m : Nat) (h : orbitEnumerate g hg n = orbitEnumerate g hg m) :
    n = m := by
  simp [orbitEnumerate] at h
  exact h

/-- [I.P04 part 2] Orbit enumeration hits every orbit ray element. -/
theorem orbit_enumerate_surjective (g : Generator) (hg : g ≠ omega)
    (x : TauObj) (hx : OrbitRay g x) :
    ∃ n, orbitEnumerate g hg n = x := by
  obtain ⟨hseed, _⟩ := hx
  exact ⟨x.depth, by
    cases x; simp [orbitEnumerate] at hseed ⊢; exact hseed.symm⟩

/-- Orbit enumeration produces elements in the orbit ray. -/
theorem orbit_enumerate_in_ray (g : Generator) (hg : g ≠ omega) (n : Nat) :
    OrbitRay g (orbitEnumerate g hg n) := by
  exact ⟨rfl, hg⟩

-- ============================================================
-- GLOBAL COUNTABILITY
-- ============================================================

/-- Encode a TauObj as a natural number: 5 * depth + seed_index.
    This gives a computable injection TauObj → Nat. -/
def tauObj_encode (x : TauObj) : Nat :=
  5 * x.depth + x.seed.toNat

/-- The encoding is injective: distinct TauObjs yield distinct codes. -/
theorem tauObj_encode_injective (x y : TauObj) (h : tauObj_encode x = tauObj_encode y) :
    x = y := by
  cases x with | mk sx dx =>
  cases y with | mk sy dy =>
  simp only [tauObj_encode] at h
  have h_seed_lt : sx.toNat < 5 := by cases sx <;> simp [Generator.toNat]
  have h_seed_lt2 : sy.toNat < 5 := by cases sy <;> simp [Generator.toNat]
  have h_depth : dx = dy := by omega
  have h_seed_nat : sx.toNat = sy.toNat := by omega
  subst h_depth
  cases sx <;> cases sy <;> simp_all [Generator.toNat]

/-- [I.P04] Obj(τ) is countable: there exists an injection TauObj → Nat. -/
theorem tauObj_countable : ∃ f : TauObj → Nat, Function.Injective f :=
  ⟨tauObj_encode, fun _ _ h => tauObj_encode_injective _ _ h⟩

end Tau.Orbit

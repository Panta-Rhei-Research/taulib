import TauLib.BookI.Sets.CantorRefutation
import TauLib.BookI.Polarity.OmegaGerms

/-!
# TauLib.BookI.Sets.UniqueInfinity

The Unique Infinity Object theorem: omega is the sole infinity, and
omega-germs with their ultrametric structure replace the cardinality hierarchy.

## Registry Cross-References

- [I.D76] Omega-Germ Approach — `OmegaGermApproach`
- [I.T36] Unique Infinity Object — `unique_infinity`
- [I.P37] Ultrametric Replaces Cardinality — `ultrametric_replaces_card`

## Ground Truth Sources
- Part IX "The Cantor Mirage": With the diagonal argument blocked,
  the cardinality hierarchy collapses to a single infinity.

## Mathematical Content

In ZF set theory, the Axiom of Infinity produces aleph_0, and then the
powerset axiom + diagonal argument produce aleph_1, aleph_2, ... --
an infinite hierarchy of cardinals.

In Category tau:
- K2 (omega fixed point) provides exactly ONE infinity object: omega
- K5 (beacon non-successor) makes omega unreachable from any orbit ray
- K6 (object closure) seals the universe: Obj(tau) = 4 orbits + {omega}
- The diagonal argument is inapplicable (I.T35)

Therefore: omega is the UNIQUE infinity object. There is no second
infinity, no aleph_1, no continuum hypothesis. The cardinality hierarchy
is replaced by a METRIC structure: the divergence ultrametric on
omega-germs (compatible towers on the primorial ladder).

Omega-germs form an inverse limit of finite rings Z/M_kZ. The
convergence mechanism is: a sequence of naturals (n_i) converges if
their omega-tails agree to ever-deeper depths. This is NOT a cardinality
notion but a proximity notion -- qualitative, not quantitative.
-/

namespace Tau.Sets

open Tau.Kernel Tau.Orbit Tau.Denotation Tau.Polarity Generator

-- ============================================================
-- OMEGA-GERM APPROACH [I.D76]
-- ============================================================

/-- [I.D76] The Omega-Germ Approach: omega-germs are compatible towers
    on the primorial ladder, equipped with the divergence ultrametric.
    This replaces "set of all reals" with "inverse limit of finite rings."

    The approach has three components:
    1. The primorial ladder M_1 | M_2 | M_3 | ... provides the tower
    2. Reduction maps pi_{l->k} : Z/M_l -> Z/M_k give compatibility
    3. The divergence ultrametric measures agreement depth -/
structure OmegaGermApproach where
  /-- The primorial ladder is well-defined: M_k > 0 for all k -/
  ladder_positive : forall k, primorial k > 0
  /-- The ladder is divisible: M_k | M_l for k <= l -/
  ladder_divisible : forall k l, k ≤ l -> primorial k ∣ primorial l
  /-- Reduction maps compose: (x mod M_l) mod M_k = x mod M_k for k <= l -/
  reduction_compatible : forall (x : TauIdx) (k l : TauIdx),
    k ≤ l -> reduce (reduce x l) k = reduce x k
  /-- The ultrametric is symmetric -/
  ultra_sym : forall (t1 t2 : OmegaTail), ultra_dist t1 t2 = ultra_dist t2 t1

/-- Construct the omega-germ approach from established lemmas. -/
def omega_germ_approach : OmegaGermApproach where
  ladder_positive := primorial_pos
  ladder_divisible := fun _ _ h => primorial_dvd h
  reduction_compatible := fun x _ _ h => reduction_compat x h
  ultra_sym := ultra_symmetric

-- ============================================================
-- UNIQUE INFINITY [I.T36]
-- ============================================================

/-- An "infinity object" in tau is an object that is a fixed point
    of rho (absorbs iteration) and is unreachable from orbit rays.
    These are precisely the defining properties of omega (K2 + K5). -/
structure InfinityObject (x : TauObj) where
  /-- Fixed under rho: rho(x) = x -/
  rho_fixed : rho x = x
  /-- Unreachable from every non-omega orbit -/
  unreachable : forall (g : Generator) (_ : g ≠ omega) (n : Nat),
    iter_rho n (TauObj.ofGen g) ≠ x

/-- Omega (with any depth) is a fixed point of rho. -/
theorem omega_rho_fixed (d : Nat) : rho ⟨omega, d⟩ = ⟨omega, d⟩ :=
  K2_omega_fixed d

/-- The canonical omega object is an infinity object. -/
def omega_is_infinity : InfinityObject omega_obj where
  rho_fixed := K2_omega_fixed 0
  unreachable := by
    intro g hg n h
    simp [omega_obj, TauObj.ofGen, iter_rho_depth g hg 0 n] at h
    exact hg h.1

/-- [I.T36] Unique Infinity Object: omega is the ONLY infinity object
    in Category tau.

    Proof: Let x be any infinity object. Since rho(x) = x and x is
    unreachable from orbit rays, x must have seed = omega (by K6
    object closure, the only objects not in orbit rays have seed omega).
    Then x = (omega, d) for some d. Since rho(omega, d) = (omega, d)
    (K2), ANY omega-seeded object is rho-fixed.

    But the uniqueness is stronger: all (omega, d) are rho-equivalent
    (they all satisfy rho(x) = x), so up to rho-equivalence there is
    exactly one infinity object. -/
theorem unique_infinity (x : TauObj) (hx : InfinityObject x) :
    x.seed = omega := by
  -- By K6 object closure, x.seed is one of the 5 generators
  rcases K6_object_closure x with h | h | h | h | h
  · -- seed = alpha: then rho(x) = (alpha, x.depth + 1) != x
    exfalso
    have hrho := hx.rho_fixed
    rw [show x = ⟨alpha, x.depth⟩ from by cases x; simp at h; simp [h]] at hrho
    simp [rho] at hrho
  · -- seed = pi: same argument
    exfalso
    have hrho := hx.rho_fixed
    rw [show x = ⟨pi, x.depth⟩ from by cases x; simp at h; simp [h]] at hrho
    simp [rho] at hrho
  · -- seed = gamma
    exfalso
    have hrho := hx.rho_fixed
    rw [show x = ⟨gamma, x.depth⟩ from by cases x; simp at h; simp [h]] at hrho
    simp [rho] at hrho
  · -- seed = eta
    exfalso
    have hrho := hx.rho_fixed
    rw [show x = ⟨eta, x.depth⟩ from by cases x; simp at h; simp [h]] at hrho
    simp [rho] at hrho
  · -- seed = omega: done
    exact h

/-- Corollary: every infinity object is in the omega fiber. -/
theorem infinity_in_omega_fiber (x : TauObj) (hx : InfinityObject x) :
    OmegaFiber x :=
  unique_infinity x hx

/-- Corollary: no non-omega generator produces an infinity object. -/
theorem no_orbit_infinity (g : Generator) (hg : g ≠ omega) (n : Nat) :
    ¬ InfinityObject ⟨g, n⟩ := by
  intro h
  have hseed := unique_infinity ⟨g, n⟩ h
  simp at hseed
  exact hg hseed

-- ============================================================
-- ULTRAMETRIC REPLACES CARDINALITY [I.P37]
-- ============================================================

/-- [I.P37] Ultrametric structure replaces cardinality hierarchy.

    In ZF, the chain aleph_0 < aleph_1 < aleph_2 < ... measures
    "how many" elements a set has. In tau, this hierarchy collapses:
    there is only one infinity (omega), and the notion of "size" is
    replaced by PROXIMITY in the divergence ultrametric.

    Two omega-tails are "close" if they agree to deep primorial depth,
    and "far" if they diverge early. This is an ultrametric (satisfies
    the strong triangle inequality), providing a finer structure than
    cardinality.

    The replacement has three pillars:
    1. The ultrametric exists (from OmegaGerms)
    2. It satisfies the strong triangle inequality (ultra_triangle)
    3. There is no second infinity to compare against (unique_infinity)

    We package these as a single theorem. -/
theorem ultrametric_replaces_card :
    -- Pillar 1: ultrametric is well-defined
    (forall (t1 t2 : OmegaTail), ultra_dist t1 t2 = ultra_dist t2 t1) /\
    -- Pillar 2: strong triangle inequality (for equal-depth tails)
    (forall (t1 t2 t3 : OmegaTail),
      t1.depth = t2.depth -> t1.depth = t3.depth ->
      ultra_dist t1 t3 = 0 ∨
      ultra_dist t1 t3 ≥ Nat.min (ultra_dist t1 t2) (ultra_dist t2 t3)) /\
    -- Pillar 3: unique infinity (no cardinality hierarchy)
    (forall (x : TauObj), InfinityObject x -> x.seed = omega) :=
  ⟨ultra_symmetric, ultra_triangle, unique_infinity⟩

-- ============================================================
-- GERM CONVERGENCE [I.D76b]
-- ============================================================

/-- Germ convergence: a sequence (n_i) of naturals "converges" if
    their omega-tails agree to ever-deeper primorial depths.
    Formally: for every depth d, there exists N such that for all
    i, j >= N, the tails of n_i and n_j at depth d are identical. -/
def GermConvergence (seq : Nat -> TauIdx) (d : Nat) : Prop :=
  exists N, forall i j, i ≥ N -> j ≥ N ->
    forall k, k < d -> reduce (seq i) (k + 1) = reduce (seq j) (k + 1)

/-- Constant sequences converge at every depth. -/
theorem const_seq_converges (c : TauIdx) (d : Nat) :
    GermConvergence (fun _ => c) d := by
  exact ⟨0, fun _ _ _ _ _ _ => rfl⟩

/-- The convergence mechanism is via primorial reduction maps:
    convergence at depth d means agreement modulo M_d. -/
theorem germ_convergence_via_reduction (seq : Nat -> TauIdx) (d : Nat) (_hd : d ≥ 1)
    (h : exists N, forall i j, i ≥ N -> j ≥ N ->
      reduce (seq i) d = reduce (seq j) d) :
    GermConvergence seq d := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun i j hi hj k hk => by
    -- reduce(seq i)(k+1) = reduce(seq j)(k+1)
    -- Since k < d, we have k+1 <= d, so M_{k+1} | M_d
    -- Therefore: reduce(seq i)(k+1) = reduce(reduce(seq i)(d))(k+1)
    --          = reduce(reduce(seq j)(d))(k+1) = reduce(seq j)(k+1)
    have hle : k + 1 ≤ d := hk
    rw [← reduction_compat (seq i) hle,
        ← reduction_compat (seq j) hle,
        hN i j hi hj]⟩

-- ============================================================
-- HIERARCHY COLLAPSE
-- ============================================================

/-- The cardinality hierarchy collapses: since omega is the unique infinity
    and the diagonal argument is inapplicable, there is exactly one
    infinite cardinal in tau (witnessed by the countable object set). -/
theorem cardinality_hierarchy_collapse :
    -- Part 1: exactly one infinity object (up to seed)
    (forall (x y : TauObj), InfinityObject x -> InfinityObject y ->
      x.seed = y.seed) /\
    -- Part 2: the universe is countable
    (exists (f : TauObj -> Nat), Function.Injective f) /\
    -- Part 3: no apparatus for producing larger infinities
    (¬ exists (_ : CantorDiagonalApparatus), True) := by
  refine ⟨?_, tauObj_countable, cantor_inapplicable⟩
  intro x y hx hy
  rw [unique_infinity x hx, unique_infinity y hy]

-- ============================================================
-- SMOKE TESTS
-- ============================================================

-- Omega is the unique infinity object
#eval omega_obj  -- { seed := omega, depth := 0 }

-- Non-omega objects are not infinity objects (verified by construction)
example : ¬ InfinityObject ⟨alpha, 5⟩ := no_orbit_infinity alpha (by decide) 5
example : ¬ InfinityObject ⟨pi, 3⟩ := no_orbit_infinity pi (by decide) 3

-- Ultrametric symmetry
example : ultra_dist (mk_omega_tail 7 5) (mk_omega_tail 42 5) =
          ultra_dist (mk_omega_tail 42 5) (mk_omega_tail 7 5) :=
  ultra_symmetric _ _

-- Constant sequence converges
example : GermConvergence (fun _ => 42) 10 := const_seq_converges 42 10

-- Primorial positivity is computable (the omega-germ approach is constructible)
#eval primorial 3  -- 30

end Tau.Sets

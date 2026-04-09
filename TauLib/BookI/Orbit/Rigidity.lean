import TauLib.BookI.Orbit.Closure

/-!
# TauLib.BookI.Orbit.Rigidity

Rigidity (Aut(τ) = {id}) and Categoricity of τ₀.

## Registry Cross-References

- [I.T07] Rigidity of τ — `rigidity_non_omega`
- [I.T08] Categoricity of τ₀ — `categoricity_non_omega`
-/

namespace Tau.Orbit

open Tau.Kernel Generator

/-- If x.seed = omega, then rho x = x (generalized K2). -/
theorem rho_seed_omega (x : TauObj) (h : x.seed = omega) : rho x = x := by
  cases x with | mk s d => simp at h; subst h; exact K2_omega_fixed d

/-- A τ-automorphism: a bijection TauObj → TauObj that commutes with ρ. -/
structure TauAutomorphism where
  toFun : TauObj → TauObj
  invFun : TauObj → TauObj
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x
  rho_comm : ∀ x, toFun (rho x) = rho (toFun x)

/-- Any τ-automorphism maps omega-fiber objects to omega-fiber objects. -/
theorem auto_omega_to_omega (φ : TauAutomorphism) (d : Nat) :
    (φ.toFun ⟨omega, d⟩).seed = omega := by
  have h1 := φ.rho_comm ⟨omega, d⟩
  rw [K2_omega_fixed] at h1
  cases hobj : φ.toFun ⟨omega, d⟩ with | mk s dep =>
  cases s with
  | omega => rfl
  | alpha | pi | gamma | eta =>
    exfalso; rw [hobj] at h1; simp [rho] at h1

/-- φ maps non-omega generators to non-omega objects. -/
theorem auto_non_omega (φ : TauAutomorphism) (g : Generator) (hg : g ≠ omega) :
    (φ.toFun ⟨g, 0⟩).seed ≠ omega := by
  intro h_om
  have h1 := φ.rho_comm ⟨g, 0⟩
  rw [K4_no_jump g hg 0] at h1
  rw [rho_seed_omega _ h_om] at h1
  have h3 := congrArg φ.invFun h1
  rw [φ.left_inv, φ.left_inv] at h3
  simp at h3

/-- For non-omega g, φ maps the orbit O_g with constant depth offset. -/
theorem auto_shift (φ : TauAutomorphism) (g : Generator) (hg : g ≠ omega) (n : Nat) :
    φ.toFun ⟨g, n⟩ = ⟨(φ.toFun ⟨g, 0⟩).seed, (φ.toFun ⟨g, 0⟩).depth + n⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := φ.rho_comm ⟨g, n⟩
    rw [K4_no_jump g hg n, ih] at h1
    rw [K4_no_jump _ (auto_non_omega φ g hg)] at h1
    rw [h1]; congr 1

/-- φ maps depth-0 non-omega objects to depth 0. -/
theorem rigidity_depth (φ : TauAutomorphism) (g : Generator) (hg : g ≠ omega) :
    (φ.toFun ⟨g, 0⟩).depth = 0 := by
  -- Find preimage y of ⟨(φ(g,0)).seed, 0⟩
  have hy_img := φ.right_inv ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩
  -- y = φ⁻¹(⟨seed, 0⟩), φ(y) = ⟨seed, 0⟩
  -- y cannot be omega-fiber
  have hy_ne : (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).seed ≠ omega := by
    intro h_om
    -- φ maps omega objects to omega objects
    have h1 := auto_omega_to_omega φ (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).depth
    -- Rewrite ⟨omega, y.depth⟩ = y (since y.seed = omega)
    have h_eta : (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩) =
        ⟨(φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).seed,
         (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).depth⟩ := by
      cases (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩); rfl
    rw [h_om] at h_eta
    rw [← h_eta] at h1
    -- h1: (φ(y)).seed = omega, but φ(y) = ⟨(φ(g,0)).seed, 0⟩
    rw [hy_img] at h1
    -- h1: (φ(g,0)).seed = omega — contradicts auto_non_omega
    exact auto_non_omega φ g hg h1
  -- Apply shift formula to y's orbit
  have h_shift := auto_shift φ
    (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).seed
    hy_ne
    (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).depth
  -- Rewrite ⟨y.seed, y.depth⟩ = y
  have h_eta2 : (⟨(φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).seed,
                   (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).depth⟩ : TauObj) =
      φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩ := by
    cases (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩); rfl
  rw [h_eta2] at h_shift
  rw [hy_img] at h_shift
  -- h_shift: ⟨(φ(g,0)).seed, 0⟩ = ⟨(φ(⟨y.seed,0⟩)).seed, (φ(⟨y.seed,0⟩)).depth + y.depth⟩
  -- Extract depth: 0 = (φ(⟨y.seed,0⟩)).depth + y.depth
  have h_dep := congrArg TauObj.depth h_shift
  simp at h_dep
  -- Both summands are 0
  have hy_depth_zero : (φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).depth = 0 := by omega
  -- y.depth = 0, so y = ⟨y.seed, 0⟩, so φ(⟨y.seed, 0⟩) = ⟨seed, 0⟩
  have h_base : φ.toFun ⟨(φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).seed, 0⟩ =
      ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩ := by
    have h_y_eq : φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩ =
        ⟨(φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).seed, 0⟩ := by
      have := h_eta2.symm
      rw [hy_depth_zero] at this
      exact this
    rw [← h_y_eq]; exact hy_img
  -- Now: φ(⟨y.seed, d₀⟩) = ⟨seed, d₀⟩ (from shift + base)
  have h_yd : φ.toFun ⟨(φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).seed, (φ.toFun ⟨g, 0⟩).depth⟩ =
      ⟨(φ.toFun ⟨g, 0⟩).seed, (φ.toFun ⟨g, 0⟩).depth⟩ := by
    have h := auto_shift φ _ hy_ne (φ.toFun ⟨g, 0⟩).depth
    have h_s := congrArg TauObj.seed h_base
    have h_d := congrArg TauObj.depth h_base
    simp at h_s h_d
    rw [h_s, h_d] at h; simpa using h
  -- φ(⟨g, 0⟩) = ⟨seed, d₀⟩ (by eta)
  have h_g : φ.toFun ⟨g, 0⟩ = ⟨(φ.toFun ⟨g, 0⟩).seed, (φ.toFun ⟨g, 0⟩).depth⟩ := by
    cases (φ.toFun ⟨g, 0⟩); rfl
  -- Injectivity gives ⟨g, 0⟩ = ⟨y.seed, d₀⟩
  have h_eq : φ.toFun ⟨g, 0⟩ = φ.toFun ⟨(φ.invFun ⟨(φ.toFun ⟨g, 0⟩).seed, 0⟩).seed,
      (φ.toFun ⟨g, 0⟩).depth⟩ := by
    rw [h_g, h_yd]
  have h_eq2 := congrArg φ.invFun h_eq
  rw [φ.left_inv, φ.left_inv] at h_eq2
  exact (congrArg TauObj.depth h_eq2).symm

/-- [I.T07] **Rigidity**: φ = id on non-omega objects (given seed preservation). -/
theorem rigidity_non_omega (φ : TauAutomorphism) (g : Generator) (hg : g ≠ omega)
    (h_seed : (φ.toFun ⟨g, 0⟩).seed = g) (n : Nat) :
    φ.toFun ⟨g, n⟩ = ⟨g, n⟩ := by
  have h_shift := auto_shift φ g hg n
  have h_depth := rigidity_depth φ g hg
  rw [h_seed, h_depth] at h_shift
  simpa using h_shift

/-- A model of the τ₀ axioms. -/
structure TauModel where
  Carrier : Type
  gen : Generator → Carrier
  rho_model : Carrier → Carrier
  gen_distinct_ax : ∀ g h : Generator, g ≠ h → gen g ≠ gen h
  omega_fixed_ax : rho_model (gen omega) = gen omega

/-- The canonical map: ⟨g, n⟩ ↦ ρ_M^n(g_M). -/
def interpret (M : TauModel) (x : TauObj) : M.Carrier :=
  Nat.rec (M.gen x.seed) (fun _ ih => M.rho_model ih) x.depth

/-- [I.T08] **Categoricity** (non-omega): unique homomorphism into any model. -/
theorem categoricity_non_omega (M : TauModel)
    (f : TauObj → M.Carrier)
    (f_gen : ∀ g, f (TauObj.ofGen g) = M.gen g)
    (f_rho : ∀ x, f (rho x) = M.rho_model (f x))
    (g : Generator) (hg : g ≠ omega) (n : Nat) :
    f ⟨g, n⟩ = interpret M ⟨g, n⟩ := by
  induction n with
  | zero => simp [interpret, TauObj.ofGen] at f_gen ⊢; exact f_gen g
  | succ n ih =>
    have h_rho := f_rho ⟨g, n⟩
    rw [K4_no_jump g hg n] at h_rho
    rw [h_rho, ih]; simp [interpret]

end Tau.Orbit

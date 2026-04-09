import TauLib.BookIII.Doors.MutualDetermination

/-!
# TauLib.BookIII.Doors.SplitComplexZeta

Split-Complex Zeta Function, Functional Equation Involution, and Bipolar Euler Product.

## Registry Cross-References

- [III.D26] Split-Complex Zeta ζ_τ — `split_zeta_b`, `split_zeta_c`, `split_zeta_check`
- [III.D27] Functional Equation Involution J — `fe_involution`, `fe_involution_check`
- [III.T16] Bipolar Euler Product — `bipolar_euler_check`

## Mathematical Content

**III.D26 (Split-Complex Zeta):** ζ_τ(s) = e₊·ζ_B(s) + e₋·ζ_C(s), encoding
the Riemann zeta in split-complex coordinates. B-lobe = B-type primes,
C-lobe = C-type primes.

**III.D27 (Functional Equation Involution):** J exchanges B-lobe and C-lobe
components: J(b, c, x) = (c, b, x). J² = id.

**III.T16 (Bipolar Euler Product):** ζ_τ(s) = ∏_p (1 - Label(p)·p^{-s})^{-1}.
CRT decomposition at each primorial level recovers the partial products.
-/

namespace Tau.BookIII.Doors

open Tau.Polarity Tau.Boundary Tau.Coordinates Tau.Denotation
open Tau.BookII.Interior Tau.BookII.Enrichment
open Tau.BookIII.Enrichment Tau.BookIII.Sectors
open Tau.BookIII.Spectral

-- ============================================================
-- SPLIT-COMPLEX ZETA [III.D26]
-- ============================================================

/-- [III.D26] B-lobe partial zeta: product of B-type primes up to depth k.
    Delegates to the label product from Trichotomy. -/
def split_zeta_b (k : TauIdx) : TauIdx := compute_label_product .B k

/-- [III.D26] C-lobe partial zeta: product of C-type primes up to depth k. -/
def split_zeta_c (k : TauIdx) : TauIdx := compute_label_product .C k

/-- [III.D26] X-type partial product (crossing prime contribution). -/
def split_zeta_x (k : TauIdx) : TauIdx := compute_label_product .X k

/-- [III.D26] Split-complex zeta check: B · C · X = Prim(k).
    The three label products account for all primes in the primorial. -/
def split_zeta_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let b_prod := split_zeta_b k
      let c_prod := split_zeta_c k
      let x_prod := split_zeta_x k
      let pk := primorial k
      let product_ok := if pk > 0 then b_prod * c_prod * x_prod == pk else true
      product_ok && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- FUNCTIONAL EQUATION INVOLUTION [III.D27]
-- ============================================================

/-- [III.D27] Functional equation involution: exchanges B-lobe and C-lobe
    components of a boundary normal form. J(b, c, x) = (c, b, x). -/
def fe_involution (nf : BoundaryNF) : BoundaryNF :=
  ⟨nf.c_part, nf.b_part, nf.x_part, nf.depth⟩

/-- [III.D27] Involution check: J² = identity for all BNFs in range. -/
def fe_involution_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let nf := boundary_normal_form x k
      let j2 := fe_involution (fe_involution nf)
      let ok := j2.b_part == nf.b_part &&
                j2.c_part == nf.c_part &&
                j2.x_part == nf.x_part
      ok && go x (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.D27] J swaps B and C but fixes X. -/
def fe_swap_check (bound db : TauIdx) : Bool :=
  go 0 1 ((bound + 1) * (db + 1))
where
  go (x k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if x > bound then true
    else if k > db then go (x + 1) 1 (fuel - 1)
    else
      let nf := boundary_normal_form x k
      let jnf := fe_involution nf
      let swap_ok := jnf.b_part == nf.c_part && jnf.c_part == nf.b_part
      let fix_ok := jnf.x_part == nf.x_part
      swap_ok && fix_ok && go x (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- BIPOLAR EULER PRODUCT [III.T16]
-- ============================================================

/-- [III.T16] Bipolar Euler product: B · C · X = Prim(k) and B, C coprime. -/
def bipolar_euler_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k > db then true
    else
      let b := split_zeta_b k
      let c := split_zeta_c k
      let x := split_zeta_x k
      let pk := primorial k
      let euler_ok := if pk > 0 then b * c * x == pk else true
      let coprime_ok := Nat.gcd b c == 1
      euler_ok && coprime_ok && go (k + 1) (fuel - 1)
  termination_by fuel

/-- [III.T16] Tower coherence: products at depth k+1 extend depth k. -/
def euler_tower_check (db : TauIdx) : Bool :=
  go 1 (db + 1)
where
  go (k fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if k >= db then true
    else
      let b_k := split_zeta_b k
      let b_k1 := split_zeta_b (k + 1)
      let b_extend := if b_k > 0 then b_k1 % b_k == 0 else true
      let c_k := split_zeta_c k
      let c_k1 := split_zeta_c (k + 1)
      let c_extend := if c_k > 0 then c_k1 % c_k == 0 else true
      b_extend && c_extend && go (k + 1) (fuel - 1)
  termination_by fuel

-- ============================================================
-- SMOKE TESTS
-- ============================================================

#eval split_zeta_b 3                       -- product of B-type primes
#eval split_zeta_c 3                       -- product of C-type primes
#eval split_zeta_x 3                       -- product of X-type primes
#eval split_zeta_check 5                   -- true
#eval fe_involution_check 15 4             -- true
#eval fe_swap_check 15 4                   -- true
#eval bipolar_euler_check 5                -- true
#eval euler_tower_check 4                  -- true

-- ============================================================
-- FORMAL VERIFICATION (native_decide)
-- ============================================================

theorem split_zeta_5 :
    split_zeta_check 5 = true := by native_decide

theorem fe_involution_15_4 :
    fe_involution_check 15 4 = true := by native_decide

theorem fe_swap_15_4 :
    fe_swap_check 15 4 = true := by native_decide

theorem bipolar_euler_5 :
    bipolar_euler_check 5 = true := by native_decide

theorem euler_tower_4 :
    euler_tower_check 4 = true := by native_decide

-- ============================================================
-- STRUCTURAL THEOREMS
-- ============================================================

/-- [III.D26] Structural: B-zeta at depth 3 = 5 (only B-type prime ≤ p₃). -/
theorem b_zeta_3 : split_zeta_b 3 = 5 := by native_decide

/-- [III.D26] Structural: C-zeta at depth 3 = 3 (only C-type prime ≤ p₃). -/
theorem c_zeta_3 : split_zeta_c 3 = 3 := by native_decide

/-- [III.D27] Structural: involution is own inverse. -/
theorem fe_involution_involutive (nf : BoundaryNF) :
    fe_involution (fe_involution nf) = nf := by
  cases nf; rfl

/-- [III.T16] Structural: B · C · X = Prim(3) at depth 3. -/
theorem euler_product_3 :
    split_zeta_b 3 * split_zeta_c 3 * split_zeta_x 3 = primorial 3 := by
  native_decide

end Tau.BookIII.Doors

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtensionExists
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Rigidity for rank-three Hopf algebras in Oort–Tate coordinates

An `OortTateThreeBasis` is explicit presentation data, not a classification
theorem. Its generator satisfies `x³ = a x`, and its comultiplication has
coefficient `c` with `2 a c = -3`. An injective bialgebra map between two such
presentations over `ℤ_[3]` is surjective: it scales the odd generator by `u`,
and compatibility with comultiplication forces `u² ∣ 3`, hence `u` is a unit.

Existence of these coordinates for arbitrary rank-three finite flat models,
and rigidity for higher-rank models killed by powers of three, remain open.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

/-- Oort–Tate coordinates for a rank-three Hopf algebra. The existence of such
coordinates is a separate classification problem. -/
structure OortTateThreeBasis (R A : Type u) [CommRing R] [CommRing A]
    [HopfAlgebra R A] where
  /-- The odd coordinate. -/
  x : A
  /-- The coefficient in the cubic equation. -/
  a : R
  /-- The coefficient in reduced comultiplication. -/
  c : R
  /-- The power basis `1, x, x²`. -/
  basis : Module.Basis (Fin 3) R A
  /-- The constant basis element. -/
  basisZero : basis 0 = 1
  /-- The linear basis element. -/
  basisOne : basis 1 = x
  /-- The quadratic basis element. -/
  basisTwo : basis 2 = x ^ 2
  /-- The cubic equation. -/
  cube : x ^ 3 = a • x
  /-- Inversion negates the coordinate. -/
  antipode : HopfAlgebra.antipode R x = -x
  /-- The addition formula. -/
  comul : Coalgebra.comul x =
    x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x + c • (x ⊗ₜ[R] (x ^ 2) + (x ^ 2) ⊗ₜ[R] x)

namespace OortTateThreeBasis

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]

/-- Expansion in Oort–Tate coordinates. -/
theorem expansion (P : OortTateThreeBasis R A) (z : A) :
    z = P.basis.repr z 0 • (1 : A) + P.basis.repr z 1 • P.x +
      P.basis.repr z 2 • P.x ^ 2 := by
  simpa only [Fin.sum_univ_three, P.basisZero, P.basisOne, P.basisTwo] using
    (P.basis.sum_repr z).symm

/-- Coordinates of the constant element. -/
@[simp] theorem repr_one (P : OortTateThreeBasis R A) :
    P.basis.repr 1 = Finsupp.single 0 1 := by
  rw [← P.basisZero, Module.Basis.repr_self]

/-- Coordinates of the odd generator. -/
@[simp] theorem repr_x (P : OortTateThreeBasis R A) :
    P.basis.repr P.x = Finsupp.single 1 1 := by
  rw [← P.basisOne, Module.Basis.repr_self]

/-- Coordinates of the square of the generator. -/
@[simp] theorem repr_sq (P : OortTateThreeBasis R A) :
    P.basis.repr (P.x ^ 2) = Finsupp.single 2 1 := by
  rw [← P.basisTwo, Module.Basis.repr_self]

/-- The odd generator is nonzero. -/
theorem x_ne_zero [Nontrivial R] (P : OortTateThreeBasis R A) : P.x ≠ 0 := by
  rw [← P.basisOne]
  exact P.basis.ne_zero 1

/-- The antipode fixes the quadratic basis element. -/
theorem antipode_sq (P : OortTateThreeBasis R A) :
    HopfAlgebra.antipode R (P.x ^ 2) = P.x ^ 2 := by
  change HopfAlgebra.antipodeAlgHom R A (P.x ^ 2) = _
  rw [map_pow]
  change (HopfAlgebra.antipode R P.x) ^ 2 = _
  rw [P.antipode, neg_sq]

/-- Extending scalars preserves an Oort–Tate power basis and its formulas. -/
def baseChange (P : OortTateThreeBasis R A) (S : Type u) [CommRing S] [Algebra R S] :
    OortTateThreeBasis S (S ⊗[R] A) where
  x := 1 ⊗ₜ[R] P.x
  a := algebraMap R S P.a
  c := algebraMap R S P.c
  basis := P.basis.baseChange S
  basisZero := by simp [P.basisZero, Algebra.TensorProduct.one_def]
  basisOne := by simp [P.basisOne]
  basisTwo := by
    simp [P.basisTwo, Algebra.TensorProduct.tmul_pow]
  cube := by
    simpa only [map_pow, map_smul, Algebra.TensorProduct.includeRight_apply,
      algebraMap_smul] using
      congrArg (Algebra.TensorProduct.includeRight (A := S) : A →ₐ[R] S ⊗[R] A) P.cube
  antipode := by
    simp [TensorProduct.antipode_def, P.antipode, TensorProduct.tmul_neg]
  comul := by
    have hs (t : (S ⊗[S] S) ⊗[R] (A ⊗[R] A)) :
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A
          (P.c • t) = P.c •
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A t :=
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A).toLinearMap
        |>.map_smul_of_tower _ _
    simp only [TensorProduct.comul_tmul, P.comul, Bialgebra.comul_one,
      TensorProduct.tmul_add, TensorProduct.tmul_smul, map_add, hs,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.one_def,
      algebraMap_smul]

/-- When two is nonzero, the anti-invariant elements are exactly the multiples
of the odd coordinate. -/
theorem eq_smul_x_of_antipode [IsDomain R] [CharZero R]
    (P : OortTateThreeBasis R A) (z : A)
    (hz : HopfAlgebra.antipode R z = -z) : z = P.basis.repr z 1 • P.x := by
  have he := P.expansion z
  have hs : HopfAlgebra.antipode R z =
      P.basis.repr z 0 • (1 : A) - P.basis.repr z 1 • P.x +
        P.basis.repr z 2 • P.x ^ 2 := by
    conv_lhs => rw [he]
    simp [P.antipode, P.antipode_sq, sub_eq_add_neg]
  have h0 : P.basis.repr z 0 = -P.basis.repr z 0 := by
    simpa using congrArg (fun w ↦ P.basis.repr w 0) (hs.symm.trans hz)
  have h2 : P.basis.repr z 2 = -P.basis.repr z 2 := by
    simpa using congrArg (fun w ↦ P.basis.repr w 2) (hs.symm.trans hz)
  have hz0 : P.basis.repr z 0 = 0 := by
    have : (2 : R) * P.basis.repr z 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  have hz2 : P.basis.repr z 2 = 0 := by
    have : (2 : R) * P.basis.repr z 2 = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  simpa [hz0, hz2] using he

/-- A bialgebra map is scalar on the odd coordinate. -/
theorem map_x [IsDomain R] [CharZero R]
    (P : OortTateThreeBasis R A) (Q : OortTateThreeBasis R B)
    (f : A →ₐc[R] B) : f P.x = Q.basis.repr (f P.x) 1 • Q.x := by
  apply Q.eq_smul_x_of_antipode
  have h := LinearMap.congr_fun (BialgHom.antipode_comp f) P.x
  change HopfAlgebra.antipode R (f P.x) = f (HopfAlgebra.antipode R P.x) at h
  simpa [P.antipode] using h

/-- The cubic parameter transforms with weight two under a nonzero scaling. -/
theorem cubic_parameter_of_map (P : OortTateThreeBasis R A)
    (Q : OortTateThreeBasis R B) (f : A →ₐc[R] B) (v : R)
    (hv : f P.x = v • Q.x) : P.a * v = v ^ 3 * Q.a := by
  have h := congrArg f P.cube
  simp only [map_pow, map_smul, hv, smul_pow, Q.cube, smul_smul] at h
  have h' := congrArg (fun w ↦ Q.basis.repr w 1) h
  simpa using h'.symm

/-- Comparing the `(x,x²)` coefficient of comultiplication gives its scaling law. -/
theorem comul_parameter_of_map (P : OortTateThreeBasis R A)
    (Q : OortTateThreeBasis R B) (f : A →ₐc[R] B) (v : R)
    (hv : f P.x = v • Q.x) : v * Q.c = P.c * v ^ 3 := by
  have h := CoalgHomClass.map_comp_comul_apply f P.x
  rw [P.comul, hv, map_smul, Q.comul] at h
  have h' := congrArg (fun w ↦ (Q.basis.tensorProduct Q.basis).repr w (1, 2)) h
  simp [hv, map_pow, smul_pow, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_smul] at h'
  linear_combination -h'

/-- Once the scaling is a unit, the map is surjective on the whole power basis. -/
theorem surjective_of_map_x (P : OortTateThreeBasis R A)
    (Q : OortTateThreeBasis R B) (f : A →ₐc[R] B) (v : R)
    (hv : f P.x = v • Q.x) (hu : IsUnit v) : Function.Surjective f := by
  obtain ⟨u, rfl⟩ := hu
  intro z
  refine ⟨Q.basis.repr z 0 • (1 : A) +
    (Q.basis.repr z 1 * (↑u⁻¹ : R)) • P.x +
    (Q.basis.repr z 2 * (↑u⁻¹ : R) ^ 2) • P.x ^ 2, ?_⟩
  simp only [map_add, map_smul, map_one, map_pow, hv, smul_pow, smul_smul]
  simpa [← mul_assoc, ← mul_pow, mul_assoc] using (Q.expansion z).symm

/-- The `(x,x²,x²)` coefficient of coassociativity gives the Oort–Tate
parameter relation multiplied by the square of the comultiplication coefficient. -/
theorem parameter_mul_sq (P : OortTateThreeBasis R A) : P.c ^ 2 * (3 + 2 * P.a * P.c) = 0 := by
  have hx3 : P.x * P.x * P.x = P.a • P.x := by
    simpa only [pow_succ, pow_zero, one_mul] using P.cube
  have hx4 : (P.x * P.x) * (P.x * P.x) = P.a • (P.x * P.x) := by
    rw [← mul_assoc, hx3, smul_mul_assoc]
  have hx2r : P.basis.repr (P.x * P.x) = Finsupp.single 2 1 := by
    simpa only [pow_two] using P.repr_sq
  have h := Coalgebra.coassoc_apply (R := R) P.x
  have h' := congrArg (fun w ↦
    (P.basis.tensorProduct (P.basis.tensorProduct P.basis)).repr w (1, (2, 2))) h
  simp only [P.comul, map_add, map_smul, TensorProduct.add_tmul,
    TensorProduct.tmul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.assoc_tmul,
    Bialgebra.comul_mul, pow_two, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    Bialgebra.comul_one, Algebra.TensorProduct.one_def, hx3, hx4,
    smul_add, hx2r, Module.Basis.tensorProduct_repr_tmul_apply,
    P.repr_one, P.repr_x, Finsupp.single_apply,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
  norm_num at h'
  linear_combination -h'

/-- In characteristic zero the comultiplication coefficient cannot vanish:
a primitive coordinate would contradict its cubic relation. -/
theorem c_ne_zero [CharZero R] (P : OortTateThreeBasis R A) : P.c ≠ 0 := by
  intro hc
  have hd : Coalgebra.comul (R := R) P.x = P.x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] P.x := by
    simpa [hc] using P.comul
  have h := congrArg (Coalgebra.comul (R := R)) P.cube
  rw [Bialgebra.comul_pow, map_smul, hd] at h
  have h' := congrArg (fun w ↦ (P.basis.tensorProduct P.basis).repr w (1, 2)) h
  have hx3 : P.x * P.x * P.x = P.a • P.x := by
    simpa only [pow_succ, pow_zero, one_mul] using P.cube
  have hx2r : P.basis.repr (P.x * P.x) = Finsupp.single 2 1 := by
    simpa only [pow_two] using P.repr_sq
  simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, hx3,
    map_add, map_smul, Module.Basis.tensorProduct_repr_tmul_apply,
    P.repr_one, P.repr_x, hx2r, Finsupp.single_apply, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
  norm_num at h'


/-- The Oort–Tate parameter relation follows from the cubic equation and
coassociativity; it is not additional presentation data. -/
theorem parameter [IsDomain R] [CharZero R] (P : OortTateThreeBasis R A) :
    2 * P.a * P.c = -3 := by
  have h := (mul_eq_zero.mp P.parameter_mul_sq).resolve_left (pow_ne_zero 2 P.c_ne_zero)
  linear_combination h

set_option maxHeartbeats 1000000 in
-- The nine tensor coefficients require repeated normalization of the antipode identities.
/-- An odd power basis determines the Oort–Tate cubic and addition formulas.
Only the power basis and the action of inversion are supplied; the Hopf laws
determine all remaining presentation data. -/
def ofOddPowerBasis [IsDomain R] [CharZero R] [Coalgebra.IsCocomm R A]
    (x : A) (b : Module.Basis (Fin 3) R A)
    (h0 : b 0 = 1) (h1 : b 1 = x) (h2 : b 2 = x ^ 2)
    (hS : HopfAlgebra.antipode R x = -x) : OortTateThreeBasis R A := by
  have hr0 : b.repr 1 = Finsupp.single 0 1 := by rw [← h0, Module.Basis.repr_self]
  have hr1 : b.repr x = Finsupp.single 1 1 := by rw [← h1, Module.Basis.repr_self]
  have hr2 : b.repr (x ^ 2) = Finsupp.single 2 1 := by rw [← h2, Module.Basis.repr_self]
  have hS2 : HopfAlgebra.antipode R (x ^ 2) = x ^ 2 := by
    change HopfAlgebra.antipodeAlgHom R A (x ^ 2) = _
    rw [map_pow]
    change (HopfAlgebra.antipode R x) ^ 2 = _
    rw [hS, neg_sq]
  have hexp (z : A) : z = b.repr z 0 • (1 : A) + b.repr z 1 • x + b.repr z 2 • x ^ 2 := by
    simpa only [Fin.sum_univ_three, h0, h1, h2] using (b.sum_repr z).symm
  have hodd (z : A) (hz : HopfAlgebra.antipode R z = -z) : z = b.repr z 1 • x := by
    have hs : HopfAlgebra.antipode R z =
        b.repr z 0 • (1 : A) - b.repr z 1 • x + b.repr z 2 • x ^ 2 := by
      conv_lhs => rw [hexp z]
      simp [hS, hS2, sub_eq_add_neg]
    have hz0 : b.repr z 0 = 0 := by
      have hc : b.repr z 0 = -b.repr z 0 := by
        simpa [hr0, hr1, hr2] using congrArg (fun w ↦ b.repr w 0) (hs.symm.trans hz)
      have : (2 : R) * b.repr z 0 = 0 := by linear_combination hc
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    have hz2 : b.repr z 2 = 0 := by
      have hc : b.repr z 2 = -b.repr z 2 := by
        simpa [hr0, hr1, hr2] using congrArg (fun w ↦ b.repr w 2) (hs.symm.trans hz)
      have : (2 : R) * b.repr z 2 = 0 := by linear_combination hc
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    simpa [hz0, hz2] using hexp z
  have hcube : x ^ 3 = b.repr (x ^ 3) 1 • x := by
    apply hodd
    change HopfAlgebra.antipodeAlgHom R A (x ^ 3) = _
    rw [map_pow]
    change (HopfAlgebra.antipode R x) ^ 3 = _
    rw [hS]
    ring
  have he : Coalgebra.counit (R := R) x = 0 := by
    have h := HopfAlgebra.counit_antipode (R := R) x
    rw [hS, map_neg] at h
    have : (2 : R) * Coalgebra.counit (R := R) x = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  let d := (b.tensorProduct b).repr (Coalgebra.comul (R := R) x)
  have hd : Coalgebra.comul (R := R) x =
      d (0, 0) • (1 ⊗ₜ[R] (1 : A)) + d (0, 1) • (1 ⊗ₜ[R] x) +
      d (0, 2) • (1 ⊗ₜ[R] (x ^ 2)) +
      (d (1, 0) • (x ⊗ₜ[R] 1) + d (1, 1) • (x ⊗ₜ[R] x) +
        d (1, 2) • (x ⊗ₜ[R] (x ^ 2))) +
      (d (2, 0) • ((x ^ 2) ⊗ₜ[R] 1) + d (2, 1) • ((x ^ 2) ⊗ₜ[R] x) +
        d (2, 2) • ((x ^ 2) ⊗ₜ[R] (x ^ 2))) := by
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_three,
      Module.Basis.tensorProduct_apply, h0, h1, h2] using
      ((b.tensorProduct b).sum_repr (Coalgebra.comul (R := R) x)).symm
  have hl := congrArg (TensorProduct.lid R A) (Coalgebra.rTensor_counit_comul (R := R) x)
  rw [hd] at hl
  have hl' : d (0, 0) • (1 : A) + d (0, 1) • x +
      d (0, 2) • x ^ 2 = x := by
    simpa [he, Bialgebra.counit_pow] using hl
  have hr := congrArg (TensorProduct.rid R A) (Coalgebra.lTensor_counit_comul (R := R) x)
  rw [hd] at hr
  have hr' : d (0, 0) • (1 : A) + d (1, 0) • x + d (2, 0) • x ^ 2 = x := by
    simpa [he, Bialgebra.counit_pow] using hr
  have h00 : d (0, 0) = 0 := by
    simpa [hr0, hr1, hr2] using congrArg (fun z ↦ b.repr z 0) hl'
  have h01 : d (0, 1) = 1 := by
    simpa [hr0, hr1, hr2] using congrArg (fun z ↦ b.repr z 1) hl'
  have h02 : d (0, 2) = 0 := by
    simpa [hr0, hr1, hr2] using congrArg (fun z ↦ b.repr z 2) hl'
  have h10 : d (1, 0) = 1 := by
    simpa [hr0, hr1, hr2] using congrArg (fun z ↦ b.repr z 1) hr'
  have h20 : d (2, 0) = 0 := by
    simpa [hr0, hr1, hr2] using congrArg (fun z ↦ b.repr z 2) hr'
  have hs := LinearMap.congr_fun (BialgHom.antipode_comp (Bialgebra.comulBialgHom R A)) x
  change HopfAlgebra.antipode R (Coalgebra.comul (R := R) x) =
    Coalgebra.comul (R := R) (HopfAlgebra.antipode R x) at hs
  rw [hS, map_neg, hd] at hs
  have hs11 : d (1, 1) = -d (1, 1) := by
    simpa [TensorProduct.antipode_def, hS, hS2, hr0, hr1, hr2] using
      congrArg (fun z ↦ (b.tensorProduct b).repr z (1, 1)) hs
  have hs22 : d (2, 2) = -d (2, 2) := by
    simpa [TensorProduct.antipode_def, hS, hS2, hr0, hr1, hr2] using
      congrArg (fun z ↦ (b.tensorProduct b).repr z (2, 2)) hs
  have h11 : d (1, 1) = 0 := by
    have : (2 : R) * d (1, 1) = 0 := by linear_combination hs11
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  have h22 : d (2, 2) = 0 := by
    have : (2 : R) * d (2, 2) = 0 := by linear_combination hs22
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  have ht := Coalgebra.comm_comul R x
  rw [hd] at ht
  have h21 : d (2, 1) = d (1, 2) := by
    simpa [hr0, hr1, hr2] using congrArg (fun z ↦ (b.tensorProduct b).repr z (1, 2)) ht
  refine { x := x
           a := b.repr (x ^ 3) 1
           c := d (1, 2)
           basis := b
           basisZero := h0
           basisOne := h1
           basisTwo := h2
           cube := hcube
           antipode := hS
           comul := ?_ }
  rw [hd]
  simp [h00, h01, h02, h10, h20, h11, h22, h21, smul_add, add_comm, add_left_comm, add_assoc]

/-- Over the unramified three-adic integers, a nonzero Oort–Tate scaling is a unit.
This is the rank-three use of the strict ramification bound `1 < 3 - 1`. -/
theorem isUnit_of_map_x {A B : Type} [CommRing A] [CommRing B]
    [HopfAlgebra ℤ_[3] A] [HopfAlgebra ℤ_[3] B]
    (P : OortTateThreeBasis ℤ_[3] A) (Q : OortTateThreeBasis ℤ_[3] B)
    (f : A →ₐc[ℤ_[3]] B) (v : ℤ_[3]) (hv : f P.x = v • Q.x) (hvn : v ≠ 0) :
    IsUnit v := by
  have hc : Q.c = P.c * v ^ 2 := by
    apply mul_left_cancel₀ hvn
    linear_combination P.comul_parameter_of_map Q f v hv
  apply PadicInt.prime_p.squarefree v
  refine ⟨-(2 * Q.a * P.c), ?_⟩
  have hp := Q.parameter
  rw [hc] at hp
  linear_combination hp

/-- Integral rigidity for injective maps between explicitly presented rank-three
Oort–Tate Hopf algebras over `ℤ_[3]`. This does not assert that every rank-three
finite flat Hopf algebra has such a presentation. -/
theorem surjective {A B : Type} [CommRing A] [CommRing B]
    [HopfAlgebra ℤ_[3] A] [HopfAlgebra ℤ_[3] B]
    (P : OortTateThreeBasis ℤ_[3] A) (Q : OortTateThreeBasis ℤ_[3] B)
    (f : A →ₐc[ℤ_[3]] B) (hf : Function.Injective f) : Function.Surjective f := by
  let v := Q.basis.repr (f P.x) 1
  have hv : f P.x = v • Q.x := P.map_x Q f
  have hvn : v ≠ 0 := by
    intro h
    apply P.x_ne_zero
    apply hf
    simpa [h] using hv
  exact P.surjective_of_map_x Q f v hv (P.isUnit_of_map_x Q f v hv hvn)

/-- The cubic parameter is nonzero in characteristic zero. -/
theorem a_ne_zero [IsDomain R] [CharZero R] (P : OortTateThreeBasis R A) : P.a ≠ 0 := by
  intro h
  have hp := P.parameter
  rw [h] at hp
  norm_num at hp

/-- The valuation of a three-adic cubic parameter is at most one. -/
theorem valuation_a_le_one {A : Type} [CommRing A] [HopfAlgebra ℤ_[3] A]
    (P : OortTateThreeBasis ℤ_[3] A) : P.a.valuation ≤ 1 := by
  have hp : P.a * (-2 * P.c) = (3 : ℤ_[3]) := by linear_combination -P.parameter
  have hc : -2 * P.c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp
    norm_num at hp
  have hv := congrArg PadicInt.valuation hp
  rw [PadicInt.valuation_mul P.a_ne_zero hc] at hv
  have hpv : PadicInt.valuation (3 : ℤ_[3]) = 1 := PadicInt.valuation_p
  rw [hpv] at hv
  omega

/-- A nonzero generic scaling between three-adic Oort–Tate presentations has
valuation zero. The integral parameter valuations can differ by at most one,
while scaling changes them by twice an integer. -/
theorem generic_scaling_valuation {A B : Type} [CommRing A] [CommRing B]
    [HopfAlgebra ℤ_[3] A] [HopfAlgebra ℤ_[3] B]
    (P : OortTateThreeBasis ℤ_[3] A) (Q : OortTateThreeBasis ℤ_[3] B)
    (v : ℚ_[3]) (hv : v ≠ 0) (h : (P.a : ℚ_[3]) = v ^ 2 * (Q.a : ℚ_[3])) :
    v.valuation = 0 := by
  have hq : (Q.a : ℚ_[3]) ≠ 0 := PadicInt.coe_ne_zero.mpr Q.a_ne_zero
  have he := congrArg Padic.valuation h
  rw [Padic.valuation_mul (pow_ne_zero 2 hv) hq, Padic.valuation_pow,
    PadicInt.valuation_coe, PadicInt.valuation_coe] at he
  have hp := P.valuation_a_le_one
  have hq := Q.valuation_a_le_one
  omega

/-- Generic maps between Oort–Tate presentations take the odd generator to an
integral multiple of the target generator, including the zero morphism. -/
theorem generic_map_x_integral {A B : Type} [CommRing A] [CommRing B]
    [HopfAlgebra ℤ_[3] A] [HopfAlgebra ℤ_[3] B]
    (P : OortTateThreeBasis ℤ_[3] A) (Q : OortTateThreeBasis ℤ_[3] B)
    (f : ℚ_[3] ⊗[ℤ_[3]] A →ₐc[ℚ_[3]] ℚ_[3] ⊗[ℤ_[3]] B) :
    ∃ v : ℤ_[3], f (1 ⊗ₜ[ℤ_[3]] P.x) =
      (v : ℚ_[3]) • (1 ⊗ₜ[ℤ_[3]] Q.x) := by
  let PK := P.baseChange ℚ_[3]
  let QK := Q.baseChange ℚ_[3]
  let v := QK.basis.repr (f PK.x) 1
  have hv : f PK.x = v • QK.x := PK.map_x QK f
  by_cases hz : v = 0
  · exact ⟨0, by simpa [hz, PK, QK, baseChange] using hv⟩
  have ha : (P.a : ℚ_[3]) = v ^ 2 * (Q.a : ℚ_[3]) := by
    apply mul_right_cancel₀ hz
    have h := PK.cubic_parameter_of_map QK f v hv
    change (P.a : ℚ_[3]) * v = v ^ 3 * (Q.a : ℚ_[3]) at h
    linear_combination h
  have hn : ‖v‖ = 1 := by
    rw [Padic.norm_eq_zpow_neg_valuation hz, P.generic_scaling_valuation Q v hz ha]
    norm_num
  exact ⟨⟨v, hn.le⟩, hv⟩

/-- Every coordinate, not only the odd generator, is integral under a generic
map between Oort–Tate presentations. -/
theorem generic_map_integral {A B : Type} [CommRing A] [CommRing B]
    [HopfAlgebra ℤ_[3] A] [HopfAlgebra ℤ_[3] B]
    (P : OortTateThreeBasis ℤ_[3] A) (Q : OortTateThreeBasis ℤ_[3] B)
    (f : ℚ_[3] ⊗[ℤ_[3]] A →ₐc[ℚ_[3]] ℚ_[3] ⊗[ℤ_[3]] B) (z : A) :
    ∃ w : B, f (1 ⊗ₜ[ℤ_[3]] z) = 1 ⊗ₜ[ℤ_[3]] w := by
  obtain ⟨v, hv⟩ := P.generic_map_x_integral Q f
  let jA : A →ₐ[ℤ_[3]] ℚ_[3] ⊗[ℤ_[3]] A := Algebra.TensorProduct.includeRight
  let jB : B →ₐ[ℤ_[3]] ℚ_[3] ⊗[ℤ_[3]] B := Algebra.TensorProduct.includeRight
  have hv' : f (jA P.x) = jB (v • Q.x) := by
    rw [map_smul]
    rw [← algebraMap_smul ℚ_[3] v]
    exact hv
  refine ⟨P.basis.repr z 0 • (1 : B) + P.basis.repr z 1 • (v • Q.x) +
    P.basis.repr z 2 • (v • Q.x) ^ 2, ?_⟩
  change f (jA z) = jB _
  conv_lhs => rw [P.expansion z]
  simp only [map_add, map_smul, map_one, map_pow, BialgHom.map_smul_of_tower, hv']

end OortTateThreeBasis
end ThreeAdicPlan

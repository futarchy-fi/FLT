/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRigidity
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Power coordinates from an inversion basis

In a reduced rank-three Hopf algebra, a basis consisting of the unit, an odd
coordinate, and an even augmentation coordinate can be changed into an
Oort–Tate power basis. Existence of the initial inversion basis is separate.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R A : Type u} [CommRing R] [IsDomain R] [CharZero R]
  [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A] [IsReduced A]
set_option maxHeartbeats 1500000 in
-- Normalizing the tensor coefficients uses the full multiplication table of a rank-three algebra.
/-- An augmentation basis diagonalizing inversion yields Oort–Tate power coordinates.
The square of the odd generator is a unit multiple of the even augmentation vector;
this follows from the Hopf identities, without a classification hypothesis. -/
theorem nonempty_oortTateThreeBasis_of_inversion_basis (x z : A) (b : Module.Basis (Fin 3) R A)
    (h0 : b 0 = 1) (h1 : b 1 = x) (h2 : b 2 = z)
    (hS : HopfAlgebra.antipode R x = -x) (hT : HopfAlgebra.antipode R z = z)
    (hez : Coalgebra.counit (R := R) z = 0) : Nonempty (OortTateThreeBasis R A) := by
  classical
  let : Module.Free R A := Module.Free.of_basis b
  have hr0 : b.repr 1 = Finsupp.single 0 1 := by rw [← h0, Module.Basis.repr_self]
  have hr1 : b.repr x = Finsupp.single 1 1 := by rw [← h1, Module.Basis.repr_self]
  have hr2 : b.repr z = Finsupp.single 2 1 := by rw [← h2, Module.Basis.repr_self]
  have he : Coalgebra.counit (R := R) x = 0 := by
    have h := HopfAlgebra.counit_antipode (R := R) x
    rw [hS, map_neg] at h
    have : (2 : R) * Coalgebra.counit (R := R) x = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  have hexp (w : A) : w = b.repr w 0 • (1 : A) + b.repr w 1 • x + b.repr w 2 • z := by
    simpa only [Fin.sum_univ_three, h0, h1, h2] using (b.sum_repr w).symm
  have hanti (w : A) : HopfAlgebra.antipode R w =
      b.repr w 0 • (1 : A) - b.repr w 1 • x + b.repr w 2 • z := by
    conv_lhs => rw [hexp w]
    simp [hS, hT, sub_eq_add_neg]
  have heps (w : A) : Coalgebra.counit (R := R) w = b.repr w 0 := by
    conv_lhs => rw [hexp w]
    simp [he, hez]
  have hodd (w : A) (hw : HopfAlgebra.antipode R w = -w) : w = b.repr w 1 • x := by
    have hw0 : b.repr w 0 = 0 := by
      have hc : b.repr w 0 = -b.repr w 0 := by
        simpa [hr0, hr1, hr2] using congrArg (fun v ↦ b.repr v 0) ((hanti w).symm.trans hw)
      have : (2 : R) * b.repr w 0 = 0 := by linear_combination hc
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    have hw2 : b.repr w 2 = 0 := by
      have hc : b.repr w 2 = -b.repr w 2 := by
        simpa [hr0, hr1, hr2] using congrArg (fun v ↦ b.repr v 2) ((hanti w).symm.trans hw)
      have : (2 : R) * b.repr w 2 = 0 := by linear_combination hc
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    simpa [hw0, hw2] using hexp w
  have heven (w : A) (hw : HopfAlgebra.antipode R w = w)
      (hε : Coalgebra.counit (R := R) w = 0) : w = b.repr w 2 • z := by
    have hw0 : b.repr w 0 = 0 := (heps w).symm.trans hε
    have hw1 : b.repr w 1 = 0 := by
      have hc : -b.repr w 1 = b.repr w 1 := by
        simpa [hr0, hr1, hr2] using congrArg (fun v ↦ b.repr v 1) ((hanti w).symm.trans hw)
      have : (2 : R) * b.repr w 1 = 0 := by linear_combination -hc
      exact (mul_eq_zero.mp this).resolve_left (by norm_num)
    simpa [hw0, hw1] using hexp w
  let a := b.repr (x * x) 2
  let r := b.repr (x * z) 1
  have hxx : x * x = a • z := by
    apply heven
    · rw [HopfAlgebra.antipode_mul_distrib, hS, neg_mul_neg]
    · simp [Bialgebra.counit_mul, he]
  have hxz : x * z = r • x := by
    apply hodd
    rw [HopfAlgebra.antipode_mul_distrib, hS, hT, neg_mul]
  have han : a ≠ 0 := by
    intro ha
    have hxn : x ≠ 0 := by rw [← h1]; exact b.ne_zero 1
    apply hxn
    apply IsNilpotent.eq_zero
    exact ⟨2, by simpa [ha, pow_two] using hxx⟩
  have hzz : z * z = r • z := by
    have h := congrArg (· * z) hxx
    rw [mul_assoc, hxz, mul_smul_comm, hxx, smul_mul_assoc, smul_comm] at h
    exact (smul_right_injective A han) h.symm
  let coeff (w : A) := (b.tensorProduct b).repr (Coalgebra.comul (R := R) w)
  have hd (w : A) : Coalgebra.comul (R := R) w =
      coeff w (0,0) • (1 ⊗ₜ[R] (1 : A)) + coeff w (0,1) • (1 ⊗ₜ[R] x) +
      coeff w (0,2) • (1 ⊗ₜ[R] z) +
      (coeff w (1,0) • (x ⊗ₜ[R] 1) + coeff w (1,1) • (x ⊗ₜ[R] x) + coeff w (1,2) • (x ⊗ₜ[R] z)) +
      (coeff w (2,0) • (z ⊗ₜ[R] 1) + coeff w (2,1) • (z ⊗ₜ[R] x) +
        coeff w (2,2) • (z ⊗ₜ[R] z)) := by
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_three,
      Module.Basis.tensorProduct_apply, h0, h1, h2] using
      ((b.tensorProduct b).sum_repr (Coalgebra.comul (R := R) w)).symm
  have hleft (w : A) (i : Fin 3) : coeff w (0,i) = b.repr w i := by
    have h := congrArg (TensorProduct.lid R A) (Coalgebra.rTensor_counit_comul (R := R) w)
    rw [hd] at h
    have h' := congrArg (fun v ↦ b.repr v i) h
    fin_cases i <;> simpa [he, hez, hr0, hr1, hr2] using h'
  have hright (w : A) (i : Fin 3) : coeff w (i,0) = b.repr w i := by
    have h := congrArg (TensorProduct.rid R A) (Coalgebra.lTensor_counit_comul (R := R) w)
    rw [hd] at h
    have h' := congrArg (fun v ↦ b.repr v i) h
    fin_cases i <;> simpa [he, hez, hr0, hr1, hr2] using h'
  have hswap (w : A) : coeff w (2,1) = coeff w (1,2) := by
    have h := Coalgebra.comm_comul R w
    rw [hd] at h
    simpa [hr0, hr1, hr2] using congrArg (fun t ↦ (b.tensorProduct b).repr t (1,2)) h
  have hs := LinearMap.congr_fun (BialgHom.antipode_comp (Bialgebra.comulBialgHom R A)) x
  change HopfAlgebra.antipode R (Coalgebra.comul (R := R) x) =
    Coalgebra.comul (R := R) (HopfAlgebra.antipode R x) at hs
  rw [hS, map_neg, hd] at hs
  have hx11 : coeff x (1,1) = 0 := by
    have hc : coeff x (1,1) = -coeff x (1,1) := by
      simpa [TensorProduct.antipode_def, hS, hT, hr0, hr1, hr2] using
        congrArg (fun t ↦ (b.tensorProduct b).repr t (1,1)) hs
    have : (2 : R) * coeff x (1,1) = 0 := by linear_combination hc
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  have hx22 : coeff x (2,2) = 0 := by
    have hc : coeff x (2,2) = -coeff x (2,2) := by
      simpa [TensorProduct.antipode_def, hS, hT, hr0, hr1, hr2] using
        congrArg (fun t ↦ (b.tensorProduct b).repr t (2,2)) hs
    have : (2 : R) * coeff x (2,2) = 0 := by linear_combination hc
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  have ht := LinearMap.congr_fun (BialgHom.antipode_comp (Bialgebra.comulBialgHom R A)) z
  change HopfAlgebra.antipode R (Coalgebra.comul (R := R) z) =
    Coalgebra.comul (R := R) (HopfAlgebra.antipode R z) at ht
  rw [hT, hd] at ht
  have hz12 : coeff z (1,2) = 0 := by
    have hc : -coeff z (1,2) = coeff z (1,2) := by
      simpa [TensorProduct.antipode_def, hS, hT, hr0, hr1, hr2] using
        congrArg (fun t ↦ (b.tensorProduct b).repr t (1,2)) ht
    have : (2 : R) * coeff z (1,2) = 0 := by linear_combination -hc
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  let c := coeff x (1,2)
  let d := coeff z (1,1)
  let e := coeff z (2,2)
  have hdx : Coalgebra.comul (R := R) x =
      x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x + c • (x ⊗ₜ[R] z + z ⊗ₜ[R] x) := by
    rw [hd]
    simp [hleft, hright, hswap, hx11, hx22, hr1, c, smul_add, add_comm, add_left_comm, add_assoc]
  have hdz : Coalgebra.comul (R := R) z =
      z ⊗ₜ[R] 1 + 1 ⊗ₜ[R] z + d • (x ⊗ₜ[R] x) + e • (z ⊗ₜ[R] z) := by
    rw [hd]
    simp [hleft, hright, hswap, hz12, hr2, d, e, add_comm, add_left_comm, add_assoc]
  have hcube : x ^ 3 = (a * r) • x := by
    rw [pow_succ, pow_two, hxx, smul_mul_assoc, mul_comm z x, hxz, smul_smul]
  have hcn : c ≠ 0 := by
    intro hc
    have h := congrArg (Coalgebra.comul (R := R)) hcube
    rw [Bialgebra.comul_pow, map_smul, hdx] at h
    have h' := congrArg (fun t ↦ (b.tensorProduct b).repr t (1,2)) h
    simp only [hc, zero_smul, add_zero, pow_succ, pow_zero, one_mul, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, hxx,
      map_add, map_smul, Module.Basis.tensorProduct_repr_tmul_apply,
      hr0, hr1, hr2, Finsupp.single_apply, Finsupp.coe_add,
      Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
    have ha' : a + (a + a) = 0 := by simpa using h'
    have ha : (3 : R) * a = 0 := by linear_combination ha'
    exact han ((mul_eq_zero.mp ha).resolve_left (by norm_num))
  have hce : e = c := by
    have h := Coalgebra.coassoc_apply (R := R) x
    have h' := congrArg (fun t ↦ (b.tensorProduct (b.tensorProduct b)).repr t (1,(2,2))) h
    simp [hdx, hdz, hr0, hr1, hr2, Algebra.TensorProduct.one_def, smul_add,
      TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul'] at h'
    exact (h'.resolve_right hcn).symm
  have had : a * d = 2 + r * c := by
    have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) z
    rw [hdz] at h
    have h' := congrArg (fun t ↦ b.repr t 2) h
    simp [hez, hS, hT, hxx, hzz, hce, hr2,
      LinearMap.mul'_apply, TensorProduct.smul_tmul'] at h'
    linear_combination -h'
  have hsquare : (r*c) * (3+2*r*c) = 0 := by
    have h := congrArg (Coalgebra.comul (R := R)) hxx
    rw [Bialgebra.comul_mul, map_smul, hdx, hdz] at h
    have h' := congrArg (fun t ↦ (b.tensorProduct b).repr t (1,1)) h
    simp [hxx, hxz, hzz, hce, hr0, hr1, hr2, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul,
      mul_comm z x, smul_smul] at h'
    linear_combination h' + had
  have hprod : (1+r*c) * (3+2*r*c) = 0 := by
    have h := congrArg (Coalgebra.comul (R := R)) hxz
    rw [Bialgebra.comul_mul, map_smul, hdx, hdz] at h
    have h' := congrArg (fun t ↦ (b.tensorProduct b).repr t (1,2)) h
    simp [hxx, hxz, hzz, hce, hr0, hr1, hr2, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul,
      mul_comm z x, smul_smul] at h'
    linear_combination h' - (1+r*c)*had
  have haunit : IsUnit a := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨2*d, ?_⟩
    linear_combination 2*had + hprod - hsquare
  obtain ⟨u, hu⟩ := haunit
  let b' := b.unitsSMul (fun i ↦ if i = 2 then u else 1)
  have hb0 : b' 0 = 1 := by simp [b', Module.Basis.unitsSMul_apply, h0]
  have hb1 : b' 1 = x := by simp [b', Module.Basis.unitsSMul_apply, h1]
  have hb2 : b' 2 = x ^ 2 := by
    simpa [b', Module.Basis.unitsSMul_apply, h2, Units.smul_def, hu, pow_two] using hxx.symm
  exact ⟨OortTateThreeBasis.ofOddPowerBasis x b' hb0 hb1 hb2 hS⟩

end ThreeAdicPlan

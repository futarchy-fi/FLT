/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistComultiplication

/-!
# Counit and antipode laws for a quadratic twist

The descended maps satisfy both counit and both antipode identities. The
constructor `hopfAlgebraOfCoassoc` records the one remaining algebraic law:
coassociativity. It requires that law as an explicit hypothesis.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace QuadraticTwist

universe v
variable {R H J A : Type v} [CommRing R] [CommRing H] [CommRing J] [CommRing A]
variable [Algebra R H] [Algebra R J] [Algebra R A]

/-- Tensor comparison commutes with evaluation by a pair of algebra maps. -/
theorem tensorBaseChange_lift (S : Type v) [CommRing S] [Algebra R S]
    (f : H →ₐ[R] A) (g : J →ₐ[R] A) (x : S ⊗[R] H) (y : S ⊗[R] J) :
    Algebra.TensorProduct.map (AlgHom.id R S) (Algebra.TensorProduct.lift f g
        (fun _ _ ↦ .all _ _)) (tensorBaseChange R S H J (x ⊗ₜ[S] y)) =
      Algebra.TensorProduct.map (AlgHom.id R S) f x *
        Algebra.TensorProduct.map (AlgHom.id R S) g y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx', add_mul]
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, hy, hy', mul_add]
    | tmul t b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm t s]

end QuadraticTwist

namespace QuadraticTwist

universe v
variable {R H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Coalgebra.IsCocomm R H]
variable (u : Rˣ) (r : R) (hr : 2 * r = 1)

local notation "D" => model (u : R) (HopfAlgebra.antipodeAlgEquiv R H)
local notation "S" => QuadraticAlgebra R (u : R) 0
local notation "eT" => modelTensorEquiv (HopfAlgebra.antipodeAlgEquiv R H)
  (HopfAlgebra.antipodeAlgEquiv R H) u (HopfAlgebra.antipode_involutive R H)
  (HopfAlgebra.antipode_involutive R H) r hr

omit [Coalgebra.IsCocomm R H] in
/-- Compatible maps on the fixed algebra commute with paired tensor evaluation. -/
theorem modelTensor_lift (f g : D →ₐ[R] D) (F G : H →ₐ[R] H)
    (hf : ∀ a : D, (f a).val = Algebra.TensorProduct.map (AlgHom.id R S) F a.val)
    (hg : ∀ a : D, (g a).val = Algebra.TensorProduct.map (AlgHom.id R S) G a.val)
    (z : D ⊗[R] D) :
    ((Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _) z : D) : S ⊗[R] H) =
      Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.TensorProduct.lift F G (fun _ _ ↦ .all _ _)) (eT z).val := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul a b =>
    rw [modelTensorEquiv_tmul, tensorBaseChange_lift]
    change (f a).val * (g b).val = _
    rw [hf, hg]

omit [Coalgebra.IsCocomm R H] in
/-- Coefficient inclusion identifies the descended counit with the scalar-extended counit. -/
theorem modelCounit_includeLeft (a : D) :
    algebraMap R (S ⊗[R] H) (counit (H := H) (u : R) r hr a) =
      Algebra.TensorProduct.map (AlgHom.id R S)
        ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H)) a.val := by
  have he : ∀ z : S ⊗[R] H,
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] H) (coefficientCounit (u : R)
        (Bialgebra.counitAlgHom R H) z) =
        Algebra.TensorProduct.map (AlgHom.id R S)
          ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H)) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s a =>
      change (s * algebraMap R S (Coalgebra.counit a)) ⊗ₜ[R] (1 : H) =
        s ⊗ₜ[R] algebraMap R H (Coalgebra.counit a)
      simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
        TensorProduct.smul_tmul]
  rw [← he]
  have h := algebraMap_modelCounit (u : R) (HopfAlgebra.antipodeAlgEquiv R H)
    (Bialgebra.counitAlgHom R H)
    (fun x ↦ AlgHom.congr_fun AlgHom.counitAlgHom_comp_antipodeAlgHom x) r hr a
  exact congrArg (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] H) h

/-- The descended antipode is a left inverse for the descended multiplication. -/
theorem antipode_left :
    (Algebra.TensorProduct.lift (antipode (H := H) (u : R)) (AlgHom.id R D)
      (fun _ _ ↦ .all _ _)).comp (comul (H := H) u r hr) =
      (Algebra.ofId R D).comp (counit (H := H) (u : R) r hr) := by
  apply AlgHom.ext
  intro a
  apply Subtype.ext
  change ((Algebra.TensorProduct.lift (antipode (H := H) (u : R)) (AlgHom.id R D)
    (fun _ _ ↦ .all _ _) (comul u r hr a) : D) : S ⊗[R] H) = _
  rw [modelTensor_lift u r hr _ _ (HopfAlgebra.antipodeAlgHom R H) (AlgHom.id R H)
    (fun _ ↦ rfl) (fun a ↦ by simp), comul_compat]
  have h : (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R H) (AlgHom.id R H)
      (fun _ _ ↦ .all _ _)).comp (Bialgebra.comulAlgHom R H) =
      (Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H) := by
    ext x
    have he : (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R H)
        (AlgHom.id R H) (fun _ _ ↦ .all _ _)).toLinearMap =
        (LinearMap.mul' R H).comp ((HopfAlgebra.antipode R).rTensor H) := by
      ext a b
      rfl
    change (Algebra.TensorProduct.lift (HopfAlgebra.antipodeAlgHom R H)
      (AlgHom.id R H) (fun _ _ ↦ .all _ _)).toLinearMap (Coalgebra.comul x) = _
    rw [he]
    exact HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) x
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp, h]
  exact (modelCounit_includeLeft u r hr a).symm

/-- The descended antipode is a right inverse for the descended multiplication. -/
theorem antipode_right :
    (Algebra.TensorProduct.lift (AlgHom.id R D) (antipode (H := H) (u : R))
      (fun _ _ ↦ .all _ _)).comp (comul (H := H) u r hr) =
      (Algebra.ofId R D).comp (counit (H := H) (u : R) r hr) := by
  apply AlgHom.ext
  intro a
  apply Subtype.ext
  change ((Algebra.TensorProduct.lift (AlgHom.id R D) (antipode (H := H) (u : R))
    (fun _ _ ↦ .all _ _) (comul u r hr a) : D) : S ⊗[R] H) = _
  rw [modelTensor_lift u r hr _ _ (AlgHom.id R H) (HopfAlgebra.antipodeAlgHom R H)
    (fun a ↦ by simp) (fun _ ↦ rfl), comul_compat]
  have h : (Algebra.TensorProduct.lift (AlgHom.id R H) (HopfAlgebra.antipodeAlgHom R H)
      (fun _ _ ↦ .all _ _)).comp (Bialgebra.comulAlgHom R H) =
      (Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H) := by
    ext x
    have he : (Algebra.TensorProduct.lift (AlgHom.id R H)
        (HopfAlgebra.antipodeAlgHom R H) (fun _ _ ↦ .all _ _)).toLinearMap =
        (LinearMap.mul' R H).comp ((HopfAlgebra.antipode R).lTensor H) := by
      ext a b
      rfl
    change (Algebra.TensorProduct.lift (AlgHom.id R H)
      (HopfAlgebra.antipodeAlgHom R H) (fun _ _ ↦ .all _ _)).toLinearMap (Coalgebra.comul x) = _
    rw [he]
    exact HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) x
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp, h]
  exact (modelCounit_includeLeft u r hr a).symm

/-- The descended counit is a left identity for the descended group law. -/
theorem counit_left :
    (Algebra.TensorProduct.lift
      ((Algebra.ofId R D).comp (counit (H := H) (u : R) r hr)) (AlgHom.id R D)
      (fun _ _ ↦ .all _ _)).comp (comul (H := H) u r hr) = AlgHom.id R D := by
  apply AlgHom.ext
  intro a
  apply Subtype.ext
  change ((Algebra.TensorProduct.lift
      ((Algebra.ofId R D).comp (counit (H := H) (u : R) r hr)) (AlgHom.id R D)
      (fun _ _ ↦ .all _ _) (comul u r hr a) : D) : S ⊗[R] H) = a.val
  rw [modelTensor_lift u r hr _ _
    ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H)) (AlgHom.id R H)
    (modelCounit_includeLeft u r hr) (fun a ↦ by simp), comul_compat]
  have h : (Algebra.TensorProduct.lift
      ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H)) (AlgHom.id R H)
      (fun _ _ ↦ .all _ _)).comp (Bialgebra.comulAlgHom R H) = AlgHom.id R H := by
    ext x
    have he : (Algebra.TensorProduct.lift
        ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H)) (AlgHom.id R H)
        (fun _ _ ↦ .all _ _)).toLinearMap =
        (TensorProduct.lid R H).toLinearMap.comp ((Coalgebra.counit (R := R)).rTensor H) := by
      ext a b
      simp [Algebra.smul_def]
    change (Algebra.TensorProduct.lift
      ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H)) (AlgHom.id R H)
      (fun _ _ ↦ .all _ _)).toLinearMap (Coalgebra.comul x) = _
    rw [he]
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.id_apply,
      TensorProduct.lid_tmul, one_smul] using
      congrArg (TensorProduct.lid R H) (Coalgebra.rTensor_counit_comul (R := R) x)
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp, h]
  simp

/-- The descended counit is a right identity for the descended group law. -/
theorem counit_right :
    (Algebra.TensorProduct.lift
      (AlgHom.id R D) ((Algebra.ofId R D).comp (counit (H := H) (u : R) r hr))
      (fun _ _ ↦ .all _ _)).comp (comul (H := H) u r hr) = AlgHom.id R D := by
  apply AlgHom.ext
  intro a
  apply Subtype.ext
  change ((Algebra.TensorProduct.lift
      (AlgHom.id R D) ((Algebra.ofId R D).comp (counit (H := H) (u : R) r hr))
      (fun _ _ ↦ .all _ _) (comul u r hr a) : D) : S ⊗[R] H) = a.val
  rw [modelTensor_lift u r hr _ _
    (AlgHom.id R H) ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H))
    (fun a ↦ by simp) (modelCounit_includeLeft u r hr), comul_compat]
  have h : (Algebra.TensorProduct.lift
      (AlgHom.id R H) ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H))
      (fun _ _ ↦ .all _ _)).comp (Bialgebra.comulAlgHom R H) = AlgHom.id R H := by
    ext x
    have he : (Algebra.TensorProduct.lift
        (AlgHom.id R H) ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H))
        (fun _ _ ↦ .all _ _)).toLinearMap =
        (TensorProduct.rid R H).toLinearMap.comp ((Coalgebra.counit (R := R)).lTensor H) := by
      ext a b
      simp [Algebra.smul_def, mul_comm]
    change (Algebra.TensorProduct.lift
      (AlgHom.id R H) ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H))
      (fun _ _ ↦ .all _ _)).toLinearMap (Coalgebra.comul x) = _
    rw [he]
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.id_apply,
      TensorProduct.rid_tmul, one_smul] using
      congrArg (TensorProduct.rid R H) (Coalgebra.lTensor_counit_comul (R := R) x)
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp, h]
  simp

/-- The left counit identity in the form required by `Bialgebra.ofAlgHom`. -/
theorem counit_comul :
    (Algebra.TensorProduct.map (counit (H := H) (u : R) r hr) (AlgHom.id R D)).comp
      (comul u r hr) = (Algebra.TensorProduct.lid R D).symm.toAlgHom := by
  have h : (Algebra.TensorProduct.lid R D).toAlgHom.comp
      (Algebra.TensorProduct.map (counit (H := H) (u : R) r hr) (AlgHom.id R D)) =
      Algebra.TensorProduct.lift ((Algebra.ofId R D).comp (counit (u : R) r hr))
        (AlgHom.id R D) (fun _ _ ↦ .all _ _) := by
    ext <;> simp [Algebra.smul_def]
  apply AlgHom.ext
  intro a
  apply (Algebra.TensorProduct.lid R D).injective
  change ((Algebra.TensorProduct.lid R D).toAlgHom.comp
    (Algebra.TensorProduct.map (counit (H := H) (u : R) r hr) (AlgHom.id R D)))
      (comul u r hr a) = _
  rw [h]
  simpa using AlgHom.congr_fun (counit_left u r hr) a

/-- The right counit identity in the form required by `Bialgebra.ofAlgHom`. -/
theorem comul_counit :
    (Algebra.TensorProduct.map (AlgHom.id R D) (counit (H := H) (u : R) r hr)).comp
      (comul u r hr) = (Algebra.TensorProduct.rid R R D).symm.toAlgHom := by
  have h : (Algebra.TensorProduct.rid R R D).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R D) (counit (H := H) (u : R) r hr)) =
      Algebra.TensorProduct.lift (AlgHom.id R D)
        ((Algebra.ofId R D).comp (counit (u : R) r hr)) (fun _ _ ↦ .all _ _) := by
    ext <;> simp [Algebra.smul_def, mul_comm]
  apply AlgHom.ext
  intro a
  apply (Algebra.TensorProduct.rid R R D).injective
  change ((Algebra.TensorProduct.rid R R D).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R D) (counit (H := H) (u : R) r hr)))
      (comul u r hr a) = _
  rw [h]
  simpa using AlgHom.congr_fun (counit_right u r hr) a

/-- Coassociativity is sufficient to complete the descended Hopf structure.
The coassociativity hypothesis is a remaining proof obligation, not an instance. -/
@[instance_reducible]
noncomputable def hopfAlgebraOfCoassoc
    (hcoassoc : (Algebra.TensorProduct.assoc R R R D D D).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul u r hr) (AlgHom.id R D)).comp (comul u r hr)) =
      (Algebra.TensorProduct.map (AlgHom.id R D) (comul u r hr)).comp (comul u r hr)) :
    HopfAlgebra R D := by
  letI : Bialgebra R D := Bialgebra.ofAlgHom (comul u r hr) (counit (u : R) r hr)
    hcoassoc (counit_comul u r hr) (comul_counit u r hr)
  exact HopfAlgebra.ofAlgHom (antipode (u : R)) (antipode_left u r hr) (antipode_right u r hr)

end QuadraticTwist

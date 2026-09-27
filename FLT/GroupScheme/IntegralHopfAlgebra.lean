/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralCoordinateAlgebra
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Hopf structures on étale integral closures

An étale integral closure commutes with tensor products, so generic comultiplication
restricts to it. Injectivity of the maps to generic tensor powers descends the
coalgebra and antipode identities. Base change recovers the original bialgebra.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace ThreeAdicPlan
attribute [local instance 100000] Algebra.toSMul Algebra.toModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Integral normalization is unchanged after an integral extension of the base. -/
def integralClosureTowerEquiv (R S B : Type) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    [Algebra.IsIntegral R S] : integralClosure S B ≃ₐ[R] integralClosure R B where
  toFun x := ⟨x.val, isIntegral_trans (R := R) (A := S) x.val x.property⟩
  invFun x := ⟨x.val, x.property.tower_top⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

section
variable (R K A : Type) [CommRing R] [IsDomain R] [Field K] [CommRing A]
  [Algebra R K] [IsFractionRing R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A] [Algebra.IsIntegral K A]

local notation "H" => integralClosure R A

variable (B : Type) [CommRing B] [Algebra K B] [Algebra R B] [IsScalarTower R K B]

/-- Extending one normalized factor to the generic fibre cancels its normalization. -/
def integralTensorGenericEquiv : H ⊗[R] B ≃ₐ[R] A ⊗[K] B :=
  (Algebra.TensorProduct.comm R H B).trans
    (((Algebra.TensorProduct.cancelBaseChange R K K B H).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := B))
        (integralClosureGenericEquiv R K A))).trans
      (Algebra.TensorProduct.comm K B A) |>.restrictScalars R)

/-- An étale normalization commutes with tensor products and integral closure. -/
def integralTensorEquiv [Algebra.Etale R H] :
    H ⊗[R] integralClosure R B ≃ₐ[R] integralClosure R (A ⊗[K] B) :=
  ((AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R H B)
    TensorProduct.toIntegralClosure_bijective_of_smooth).restrictScalars R).trans
    ((integralClosureTowerEquiv R H (H ⊗[R] B)).trans
      (AlgEquiv.mapIntegralClosure (integralTensorGenericEquiv R K A B)))

/-- The normalization comparison sends pure tensors to the same pure tensors. -/
@[simp] theorem integralTensorEquiv_tmul [Algebra.Etale R H] (a : H) (b : integralClosure R B) :
    (integralTensorEquiv R K A B (a ⊗ₜ[R] b) : A ⊗[K] B) =
      (a : A) ⊗ₜ[K] (b : B) := by
  simp [integralTensorEquiv, integralClosureTowerEquiv, TensorProduct.toIntegralClosure,
    integralTensorGenericEquiv, integralClosureGenericEquiv, integralClosureGenericMap]

end
section Descent
variable (R K A : Type) [CommRing R] [IsDomain R] [Field K] [CommRing A]
  [Algebra R K] [IsFractionRing R K] [HopfAlgebra K A] [Algebra R A]
  [IsScalarTower R K A] [Algebra.IsIntegral K A]

local notation "H" => integralClosure R A
variable [Algebra.Etale R (integralClosure R A)]
local notation "e₂" => integralTensorEquiv R K A A

/-- Generic comultiplication restricted to the étale integral closure. -/
def integralComul : H →ₐ[R] H ⊗[R] H :=
  (e₂).symm.toAlgHom.comp ((Bialgebra.comulAlgHom K A).restrictScalars R).mapIntegralClosure

/-- The canonical map from integral to generic tensor squares. -/
def integralTensorMap : H ⊗[R] H →ₐ[R] A ⊗[K] A :=
  (integralClosure R (A ⊗[K] A)).val.comp (e₂).toAlgHom

/-- The tensor-square map preserves pure tensors. -/
@[simp] theorem integralTensorMap_tmul (a b : H) :
    integralTensorMap R K A (a ⊗ₜ[R] b) = (a : A) ⊗ₜ[K] (b : A) :=
  integralTensorEquiv_tmul R K A A a b

/-- The integral tensor square embeds in the generic tensor square. -/
theorem integralTensorMap_injective : Function.Injective (integralTensorMap R K A) :=
  Subtype.val_injective.comp (e₂).injective

/-- Integral comultiplication agrees with generic comultiplication. -/
@[simp] theorem integralTensorMap_comul (a : H) :
    integralTensorMap R K A (integralComul R K A a) = Bialgebra.comulAlgHom K A a := by
  simp [integralTensorMap, integralComul]

/-- The canonical map from integral to generic triple tensors. -/
def integralTripleMap : H ⊗[R] (H ⊗[R] H) →ₐ[R] A ⊗[K] (A ⊗[K] A) :=
  ((integralClosure R (A ⊗[K] (A ⊗[K] A))).val.comp
    (integralTensorEquiv R K A (A ⊗[K] A)).toAlgHom).comp
    (Algebra.TensorProduct.map (AlgHom.id R H) (e₂).toAlgHom)

/-- The triple-tensor map separates its first factor. -/
@[simp] theorem integralTripleMap_tmul (a : H) (z : H ⊗[R] H) :
    integralTripleMap R K A (a ⊗ₜ[R] z) = (a : A) ⊗ₜ[K] integralTensorMap R K A z := by
  simp [integralTripleMap, integralTensorMap]

/-- Integral triple tensors embed in generic triple tensors. -/
theorem integralTripleMap_injective : Function.Injective (integralTripleMap R K A) := by
  exact Subtype.val_injective.comp
    ((integralTensorEquiv R K A (A ⊗[K] A)).injective.comp
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := H)) e₂).injective)

/-- The triple-tensor map respects reassociation. -/
theorem integralTripleMap_assoc_tmul (z : H ⊗[R] H) (b : H) :
    integralTripleMap R K A (Algebra.TensorProduct.assoc R R R H H H (z ⊗ₜ[R] b)) =
      Algebra.TensorProduct.assoc K K K A A A
        (integralTensorMap R K A z ⊗ₜ[K] (b : A)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a c => simp
  | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]

/-- The triple-tensor map respects comultiplication on the right. -/
theorem integralTripleMap_rightComul (z : H ⊗[R] H) :
    integralTripleMap R K A
      (Algebra.TensorProduct.map (AlgHom.id R H) (integralComul R K A) z) =
      Algebra.TensorProduct.map (AlgHom.id K A) (Bialgebra.comulAlgHom K A)
        (integralTensorMap R K A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- The triple-tensor map respects comultiplication on the left. -/
theorem integralTripleMap_leftComul (z : H ⊗[R] H) :
    integralTripleMap R K A (Algebra.TensorProduct.assoc R R R H H H
      (Algebra.TensorProduct.map (integralComul R K A) (AlgHom.id R H) z)) =
      Algebra.TensorProduct.assoc K K K A A A
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom K A) (AlgHom.id K A)
          (integralTensorMap R K A z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [integralTripleMap_assoc_tmul]
  | add x y hx hy => simp [hx, hy]

/-- Coassociativity descends along the injective triple-tensor map. -/
theorem integralComul_coassoc :
    (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
      ((Algebra.TensorProduct.map (integralComul R K A) (.id R H)).comp
        (integralComul R K A)) =
      (Algebra.TensorProduct.map (.id R H) (integralComul R K A)).comp (integralComul R K A) := by
  ext a
  apply integralTripleMap_injective R K A
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    integralTripleMap_leftComul, integralTripleMap_rightComul, integralTensorMap_comul]
  exact Coalgebra.coassoc_apply (R := K) (a : A)

variable [IsIntegrallyClosed R]
local notation "ε" => integralClosureCounit R K A (Bialgebra.counitAlgHom K A)

/-- The left integral counit agrees with its generic counterpart. -/
theorem integralCounit_leftTensor (z : H ⊗[R] H) :
    ((Algebra.TensorProduct.lid R H)
      (Algebra.TensorProduct.map ε (AlgHom.id R H) z) : A) =
    Algebra.TensorProduct.lid K A
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K A) (AlgHom.id K A)
        (integralTensorMap R K A z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.lid_tmul, integralTensorMap_tmul]
    rw [Subalgebra.coe_smul, ← IsScalarTower.algebraMap_smul K,
      algebraMap_integralClosureCounit]

/-- The right integral counit agrees with its generic counterpart. -/
theorem integralCounit_rightTensor (z : H ⊗[R] H) :
    ((Algebra.TensorProduct.rid R R H)
      (Algebra.TensorProduct.map (AlgHom.id R H) ε z) : A) =
    Algebra.TensorProduct.rid K K A
      (Algebra.TensorProduct.map (AlgHom.id K A) (Bialgebra.counitAlgHom K A)
        (integralTensorMap R K A z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.rid_tmul, integralTensorMap_tmul]
    rw [Subalgebra.coe_smul, ← IsScalarTower.algebraMap_smul K,
      algebraMap_integralClosureCounit]

/-- The descended comultiplication satisfies the left counit identity. -/
theorem integralComul_leftCounit :
    (Algebra.TensorProduct.map ε (.id R H)).comp (integralComul R K A) =
      (Algebra.TensorProduct.lid R H).symm := by
  ext a
  apply (Algebra.TensorProduct.lid R H).injective
  apply Subtype.ext
  simp only [AlgHom.comp_apply, integralCounit_leftTensor, integralTensorMap_comul,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  change TensorProduct.lid K A
    (Coalgebra.counit.rTensor A (Coalgebra.comul (R := K) (a : A))) = (a : A)
  rw [Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

/-- The descended comultiplication satisfies the right counit identity. -/
theorem integralComul_rightCounit :
    (Algebra.TensorProduct.map (.id R H) ε).comp (integralComul R K A) =
      (Algebra.TensorProduct.rid R R H).symm := by
  ext a
  apply (Algebra.TensorProduct.rid R R H).injective
  apply Subtype.ext
  simp only [AlgHom.comp_apply, integralCounit_rightTensor, integralTensorMap_comul,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  change TensorProduct.rid K A
    (Coalgebra.counit.lTensor A (Coalgebra.comul (R := K) (a : A))) = (a : A)
  rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

/-- The bialgebra structure on an étale integral closure. -/
@[instance_reducible] def integralClosureBialgebra : Bialgebra R H :=
  Bialgebra.ofAlgHom (integralComul R K A) ε
    (integralComul_coassoc R K A) (integralComul_leftCounit R K A)
    (integralComul_rightCounit R K A)

/-- The generic antipode preserves integral elements. -/
def integralAntipodeMap : H →ₐ[R] H :=
  ((HopfAlgebra.antipodeAlgHom K A).restrictScalars R).mapIntegralClosure

omit [IsDomain R] [IsFractionRing R K] [Algebra.IsIntegral K A]
  [Algebra.Etale R (integralClosure R A)] [IsIntegrallyClosed R] in
/-- The integral antipode is the restriction of the generic antipode. -/
@[simp] theorem coe_integralAntipodeMap (a : H) :
    (integralAntipodeMap R K A a : A) = HopfAlgebra.antipode K (a : A) := rfl

omit [IsIntegrallyClosed R] in
/-- Left integral convolution agrees with generic convolution. -/
theorem integralAntipode_leftTensor (z : H ⊗[R] H) :
    ((Algebra.TensorProduct.lift (integralAntipodeMap R K A) (.id R H)
      (fun _ _ ↦ Commute.all _ _)) z : A) =
    LinearMap.mul' K A ((HopfAlgebra.antipode K).rTensor A (integralTensorMap R K A z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp [Algebra.TensorProduct.lift_tmul, integralAntipodeMap]

omit [IsIntegrallyClosed R] in
/-- Right integral convolution agrees with generic convolution. -/
theorem integralAntipode_rightTensor (z : H ⊗[R] H) :
    ((Algebra.TensorProduct.lift (.id R H) (integralAntipodeMap R K A)
      (fun _ _ ↦ Commute.all _ _)) z : A) =
    LinearMap.mul' K A ((HopfAlgebra.antipode K).lTensor A (integralTensorMap R K A z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a b => simp [Algebra.TensorProduct.lift_tmul, integralAntipodeMap]

/-- The Hopf algebra structure on an étale integral closure. -/
@[instance_reducible] def integralClosureHopfAlgebra : HopfAlgebra R H := by
  letI := integralClosureBialgebra R K A
  refine HopfAlgebra.ofAlgHom (integralAntipodeMap R K A) ?_ ?_
  · ext a
    change ((Algebra.TensorProduct.lift (integralAntipodeMap R K A) (.id R H)
      (fun _ _ ↦ Commute.all _ _)) (integralComul R K A a) : A) = algebraMap R A (ε a)
    rw [integralAntipode_leftTensor, integralTensorMap_comul, Bialgebra.comulAlgHom_apply,
      HopfAlgebra.mul_antipode_rTensor_comul_apply (R := K) (a : A),
      IsScalarTower.algebraMap_apply R K A, algebraMap_integralClosureCounit]
    rfl
  · ext a
    change ((Algebra.TensorProduct.lift (.id R H) (integralAntipodeMap R K A)
      (fun _ _ ↦ Commute.all _ _)) (integralComul R K A a) : A) = algebraMap R A (ε a)
    rw [integralAntipode_rightTensor, integralTensorMap_comul, Bialgebra.comulAlgHom_apply,
      HopfAlgebra.mul_antipode_lTensor_comul_apply (R := K) (a : A),
      IsScalarTower.algebraMap_apply R K A, algebraMap_integralClosureCounit]
    rfl

omit [IsIntegrallyClosed R] in
/-- Base change identifies the integral and generic tensor-square maps. -/
theorem integralGenericTensorMap (z : H ⊗[R] H) :
    Algebra.TensorProduct.map (integralClosureGenericEquiv R K A).toAlgHom
      (integralClosureGenericEquiv R K A).toAlgHom
      ((HopfAlgebra.IntegralClosure.baseChangeTensorEquiv R K H H).symm (1 ⊗ₜ[R] z)) =
      integralTensorMap R K A z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
  | tmul a b =>
    simp [HopfAlgebra.IntegralClosure.baseChangeTensorEquiv,
      integralClosureGenericEquiv, integralClosureGenericMap]

set_option maxHeartbeats 800000 in
-- Comparing base-change comultiplications unfolds both constructed Hopf structures.
/-- The generic-fibre normalization equivalence preserves the bialgebra structure. -/
def integralGenericBialgEquiv :
    letI := integralClosureHopfAlgebra R K A
    K ⊗[R] H ≃ₐc[K] A := by
  letI := integralClosureHopfAlgebra R K A
  refine BialgEquiv.ofAlgEquiv (integralClosureGenericEquiv R K A) ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    ext a
    change Bialgebra.counitAlgHom K A (integralClosureGenericEquiv R K A (1 ⊗ₜ[R] a)) =
      Coalgebra.counit (R := K) (1 ⊗ₜ[R] a : K ⊗[R] H)
    simp only [integralClosureGenericEquiv, AlgEquiv.ofBijective_apply,
      integralClosureGenericMap_tmul, one_smul, TensorProduct.counit_tmul,
      CommSemiring.counit_apply]
    change Bialgebra.counitAlgHom K A (a : A) = (ε a) • (1 : K)
    rw [Algebra.smul_def, mul_one, algebraMap_integralClosureCounit]
  · apply Algebra.TensorProduct.ext_ring
    ext a
    change Algebra.TensorProduct.map (integralClosureGenericEquiv R K A).toAlgHom
      (integralClosureGenericEquiv R K A).toAlgHom
      (Coalgebra.comul (R := K) (1 ⊗ₜ[R] a : K ⊗[R] H)) =
      Bialgebra.comulAlgHom K A (integralClosureGenericEquiv R K A (1 ⊗ₜ[R] a))
    have he := HopfAlgebra.IntegralClosure.baseChange_comul_includeRight R K H a
    simp only [Algebra.TensorProduct.includeRight_apply] at he
    rw [← (HopfAlgebra.IntegralClosure.baseChangeTensorEquiv R K H H).symm_apply_apply
      (Coalgebra.comul (R := K) (1 ⊗ₜ[R] a : K ⊗[R] H)), he]
    rw [integralGenericTensorMap]
    change integralTensorMap R K A (integralComul R K A a) =
      Bialgebra.comulAlgHom K A (integralClosureGenericEquiv R K A (1 ⊗ₜ[R] a))
    simp [integralClosureGenericEquiv, integralClosureGenericMap]

/-- Cocommutativity descends to the étale integral closure. -/
theorem integralClosureCocomm [Coalgebra.IsCocomm K A] :
    letI := integralClosureHopfAlgebra R K A
    Coalgebra.IsCocomm R H := by
  let := integralClosureHopfAlgebra R K A
  have hc (z : H ⊗[R] H) :
      integralTensorMap R K A (TensorProduct.comm R H H z) =
        TensorProduct.comm K A A (integralTensorMap R K A z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  constructor
  apply LinearMap.ext
  intro a
  apply integralTensorMap_injective R K A
  change integralTensorMap R K A (TensorProduct.comm R H H (integralComul R K A a)) =
    integralTensorMap R K A (integralComul R K A a)
  rw [hc, integralTensorMap_comul]
  exact Coalgebra.comm_comul (R := K) (a : A)

end Descent
end ThreeAdicPlan

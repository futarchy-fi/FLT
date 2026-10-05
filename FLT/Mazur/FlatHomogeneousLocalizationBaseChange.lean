/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousLocalizationBaseChange

/-!
# Flat base change of homogeneous localizations

Flatness preserves the inclusion into the ordinary localization. Comparing
with ordinary localization base change makes the homogeneous comparison
injective; homogeneous fraction expansion supplies surjectivity.
-/

@[expose] public noncomputable section
open HomogeneousLocalization
open scoped TensorProduct FLT.Mazur.HomogeneousLocalizationScalars
universe u
namespace FLT.Mazur.FlatHomogeneousLocalizationBaseChange
open GradedProjBaseChangeMap HomogeneousLocalizationScalars HomogeneousLocalizationBaseChange
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Ordinary localization commutes with scalar extension. -/
def ordinaryEquiv : B ⊗[R] Localization.Away f ≃ₐ[B] Localization.Away (inclusion (B := B) 𝒜 f) :=
  IsLocalization.Away.tensorProductEquivTMulRight R B f (Localization.Away f)

/-- The tensor product of the homogeneous-to-ordinary localization inclusion. -/
def tensorVal : B ⊗[R] Away 𝒜 f →ₐ[B] B ⊗[R] Localization.Away f :=
  Algebra.TensorProduct.map (AlgHom.id B B) (valAlgHom 𝒜 f)

/-- The ordinary localization map induced by scalar extension. -/
def ordinaryMap : Localization.Away f →+* Localization.Away (inclusion (B := B) 𝒜 f) :=
  IsLocalization.map (M := Submonoid.powers f) (S := Localization.Away f)
    (T := Submonoid.powers (inclusion (B := B) 𝒜 f)) _
    (inclusion (B := B) 𝒜).toRingHom (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, ((inclusion 𝒜).map_pow f n).symm⟩)

/-- Ordinary base change agrees with the localization map on the original ring. -/
lemma ordinaryEquiv_one_tmul (x : Localization.Away f) :
    ordinaryEquiv (B := B) 𝒜 f (1 ⊗ₜ[R] x) = ordinaryMap (B := B) 𝒜 f x := by
  have h : (ordinaryEquiv (B := B) 𝒜 f).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom = ordinaryMap (B := B) 𝒜 f := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply, ordinaryMap, IsLocalization.map_eq]
    exact IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := R) (S := B) A f
      (Localization.Away f) 1 a
  exact RingHom.congr_fun h x

/-- Forgetting homogeneity commutes with the localization map. -/
lemma val_awayMap (x : Away 𝒜 f) :
    (Away.map (inclusion (B := B) 𝒜) f x).val = ordinaryMap (B := B) 𝒜 f x.val := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  simp only [Away.map, HomogeneousLocalization.map_mk, val_mk,
    ordinaryMap, Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

/-- The homogeneous comparison is the restriction of ordinary localization base change. -/
lemma comparison_val (x : B ⊗[R] Away 𝒜 f) :
    (comparison (B := B) 𝒜 f x).val = ordinaryEquiv (B := B) 𝒜 f (tensorVal 𝒜 f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
    rw [comparison_tmul, HomogeneousLocalization.val_smul, val_awayMap]
    change b • ordinaryMap (B := B) 𝒜 f x.val = ordinaryEquiv 𝒜 f (b ⊗ₜ[R] x.val)
    rw [show b ⊗ₜ[R] x.val = b • (1 ⊗ₜ[R] x.val) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, ordinaryEquiv_one_tmul]
  | add x y hx hy => simp only [map_add, val_add, hx, hy]

/-- Flat scalar extension preserves the inclusion into ordinary localization. -/
lemma tensorVal_injective [Module.Flat R B] : Function.Injective (tensorVal (B := B) 𝒜 f) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (valAlgHom 𝒜 f).toLinearMap (valAlgHom_injective 𝒜 f)

/-- The homogeneous-localization comparison is injective for a flat scalar extension. -/
lemma comparison_injective [Module.Flat R B] : Function.Injective (comparison (B := B) 𝒜 f) := by
  intro x y h
  apply tensorVal_injective 𝒜 f
  apply (ordinaryEquiv 𝒜 f).injective
  rw [← comparison_val, ← comparison_val, h]

/-- Flat base change commutes with degree-zero localization at a homogeneous element. -/
def equiv [Module.Flat R B] {d : ℕ} (hf : f ∈ 𝒜 d) :
    B ⊗[R] Away 𝒜 f ≃ₐ[B] Away (baseGrade (B := B) 𝒜) (inclusion 𝒜 f) :=
  AlgEquiv.ofBijective (comparison 𝒜 f)
    ⟨comparison_injective 𝒜 f, comparison_surjective 𝒜 f hf⟩

end FLT.Mazur.FlatHomogeneousLocalizationBaseChange

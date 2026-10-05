/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricCoactionUnits

/-!
# Geometric overlaps are determined by reconstructed unit sections

Every geometric overlap gives a linear map by inserting the tensor unit.
The other scalar action recovers the entire overlap from this map. A
reconstruction chart reduces equality further to its base unit sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] tensorEquiv
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- Insert the unit before applying the overlap in tensor coordinates. -/
def overlapCoaction (e : Overlap R S M) : coefficients S M →ₗ[S] S ⊗[R] coefficients S M where
  toFun n := tensorEquiv R S M e (n ⊗ₜ[R] (1 : S))
  map_add' n m := by rw [add_tmul, map_add]
  map_smul' s n := by rw [← smul_tmul', _root_.map_smul]; rfl

/-- The overlap coaction evaluates the overlap on a unit tensor. -/
theorem overlapCoaction_apply (e : Overlap R S M) (n : coefficients S M) :
    overlapCoaction R S M e n = tensorEquiv R S M e (n ⊗ₜ[R] (1 : S)) := rfl

/-- The coaction determines an overlap without diagonal or cocycle hypotheses. -/
theorem overlapCoaction_injective : Function.Injective (overlapCoaction R S M) := by
  intro e f h
  apply tensorEquiv_injective R S M
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro n s
  have he := tensorEquiv_other_smul R S M e n s 1
  have hf := tensorEquiv_other_smul R S M f n s 1
  simp only [mul_one] at he hf
  change tensorEquiv R S M e (n ⊗ₜ[R] s) = tensorEquiv R S M f (n ⊗ₜ[R] s)
  rw [he, hf, ← overlapCoaction_apply, ← overlapCoaction_apply, h]
end FLT.Mazur.AffineGeometricOverlap

namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricOverlap AffineOverlapPullback AffinePullbackCoefficientRecognition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] overlapCoaction
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (A : (Spec R).Modules) [A.IsQuasicoherent]
variable {M : (Spec S).Modules} [M.IsQuasicoherent]
variable (e : (pullback (Spec.map φ)).obj A ≅ M)

/-- A reconstruction chart reduces overlap equality to its base unit tensors. -/
theorem overlap_eq_of_base_units :
    let := φ.hom.toAlgebra
    let := Module.compHom (coefficients S M) φ.hom
    let : IsScalarTower R S (coefficients S M) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    ∀ v w : Overlap R S M,
      (∀ m : moduleSpecΓFunctor.obj A,
        overlapCoaction R S M v ((chart φ A e).hom
          ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m)) =
        overlapCoaction R S M w ((chart φ A e).hom
          ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m))) → v = w := by
  let := φ.hom.toAlgebra
  let := Module.compHom (coefficients S M) φ.hom
  let : IsScalarTower R S (coefficients S M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  intro _ _ _ v w h
  apply overlapCoaction_injective R S M
  have hm : ModuleCat.ofHom (overlapCoaction R S M v) =
      ModuleCat.ofHom (overlapCoaction R S M w) := by
    apply (cancel_epi (chart φ A e).hom).mp
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    exact h m
  exact congrArg ModuleCat.Hom.hom hm

/-- An overlap is determined by its action on reconstructed base unit sections. -/
theorem overlap_eq_of_section_units :
    let := φ.hom.toAlgebra
    ∀ v w : Overlap R S M,
      (∀ m : moduleSpecΓFunctor.obj A,
        moduleSpecΓFunctor.map v.hom (AffineIteratedPullbackSections.specUnit
          (CommRingCat.ofHom (AffineOverlapTensor.left R S)) M
          (moduleSpecΓFunctor.map e.hom (AffineIteratedPullbackSections.specUnit φ A m))) =
        moduleSpecΓFunctor.map w.hom (AffineIteratedPullbackSections.specUnit
          (CommRingCat.ofHom (AffineOverlapTensor.left R S)) M
          (moduleSpecΓFunctor.map e.hom (AffineIteratedPullbackSections.specUnit φ A m)))) →
      v = w := by
  let := φ.hom.toAlgebra
  let := Module.compHom (coefficients S M) φ.hom
  let : IsScalarTower R S (coefficients S M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  intro _ v w h
  apply overlap_eq_of_base_units φ A e v w
  intro m
  apply (secondSections R S M).injective
  rw [overlapCoaction_apply, overlapCoaction_apply, tensorEquiv_sections,
    tensorEquiv_sections, firstSections_tmul]
  simp only [← Algebra.TensorProduct.one_def, one_smul]
  rw [chart_unit]
  exact h m

end FLT.Mazur.AffineGeometricDescentRecognition

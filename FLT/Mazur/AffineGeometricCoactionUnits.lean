/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricChartRecognition
public import FLT.Mazur.AffineIteratedPullbackSections

/-!
# Coaction compatibility detected on actual overlap unit sections

Scalar-extension maps are determined on unit tensors. The tensor section
comparisons turn that criterion into equality of actual geometric overlap
sections obtained from the base sheaf through a reconstruction chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricDescent AffinePullbackCoefficientRecognition
open AffineOverlapPullback AffineGeometricOverlap AffineTensorCocycle
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] toDatum tensorEquiv
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)

/-- The geometric coaction has the specified actual overlap section map. -/
theorem coalgebra_sections (n : coefficients S M) :
    let := φ.hom.toAlgebra
    let := Module.compHom (coefficients S M) φ.hom
    let : IsScalarTower R S (coefficients S M) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    secondSections R S M ((coalgebra φ M D).a n) =
      moduleSpecΓFunctor.map D.val.hom (firstSections R S M (n ⊗ₜ[R] (1 : S))) := by
  let := φ.hom.toAlgebra
  let := Module.compHom (coefficients S M) φ.hom
  let : IsScalarTower R S (coefficients S M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  rw [coalgebra_coaction_apply, toDatum_coaction_apply]
  exact tensorEquiv_sections R S M D.val _

/-- A fixed coaction element is exactly an equal pair of geometric unit sections. -/
theorem coalgebra_unit_iff (n : coefficients S M) :
    let := φ.hom.toAlgebra
    (coalgebra φ M D).a n =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) n ↔
    moduleSpecΓFunctor.map D.val.hom
        (AffineIteratedPullbackSections.specUnit
          (CommRingCat.ofHom (AffineOverlapTensor.left R S)) M n) =
      AffineIteratedPullbackSections.specUnit
        (CommRingCat.ofHom (AffineOverlapTensor.right R S)) M n := by
  let := φ.hom.toAlgebra
  let := Module.compHom (coefficients S M) φ.hom
  let : IsScalarTower R S (coefficients S M) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  change (coalgebra φ M D).a n = (1 : S) ⊗ₜ[R] n ↔ _
  rw [← (secondSections R S M).injective.eq_iff, coalgebra_sections]
  rw [firstSections_tmul, secondSections_tmul]
  simp only [← Algebra.TensorProduct.one_def, one_smul,
    AffineIteratedPullbackSections.specUnit_apply]

variable (A : (Spec R).Modules) [A.IsQuasicoherent]
variable (e : (pullback (Spec.map φ)).obj A ≅ M)

/-- Coaction compatibility can be checked only on the base unit tensors. -/
theorem coactionCompatible_iff_unit :
    CoactionCompatible φ A D e ↔ ∀ m : moduleSpecΓFunctor.obj A,
      (coalgebra φ M D).a ((chart φ A e).hom
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m)) =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app
        ((ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M))
        ((chart φ A e).hom ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m)) := by
  constructor
  · intro h m
    exact (congrArg (fun f ↦ f ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m))
      h).symm
  · intro h
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    exact (h m).symm

omit [M.IsQuasicoherent] in
/-- The coefficient chart sends unit tensors to reconstructed pullback sections. -/
theorem chart_unit (m : moduleSpecΓFunctor.obj A) :
    (chart φ A e).hom ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m) =
      moduleSpecΓFunctor.map e.hom (AffineIteratedPullbackSections.specUnit φ A m) := by
  change moduleSpecΓFunctor.map e.hom ((AffineModulePullbackSections.sectionsIso φ A).hom
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ m)) = _
  rw [AffineModulePullbackSections.sectionsIso_unit]
  rfl

/-- Compatibility is precisely the overlap equation on reconstructed base sections. -/
theorem coactionCompatible_iff_overlap_unit :
    let := φ.hom.toAlgebra
    CoactionCompatible φ A D e ↔ ∀ m : moduleSpecΓFunctor.obj A,
      moduleSpecΓFunctor.map D.val.hom
          (AffineIteratedPullbackSections.specUnit
            (CommRingCat.ofHom (AffineOverlapTensor.left R S)) M
            (moduleSpecΓFunctor.map e.hom (AffineIteratedPullbackSections.specUnit φ A m))) =
        AffineIteratedPullbackSections.specUnit
          (CommRingCat.ofHom (AffineOverlapTensor.right R S)) M
          (moduleSpecΓFunctor.map e.hom (AffineIteratedPullbackSections.specUnit φ A m)) := by
  let := φ.hom.toAlgebra
  rw [coactionCompatible_iff_unit]
  apply forall_congr'
  intro m
  rw [chart_unit]
  exact coalgebra_unit_iff φ D _

end FLT.Mazur.AffineGeometricDescentRecognition

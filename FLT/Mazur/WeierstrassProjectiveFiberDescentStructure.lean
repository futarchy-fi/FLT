/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure
public import FLT.Mazur.WeierstrassConicZeroProjectiveDescent
public import FLT.Mazur.WeierstrassModificationXFullFiberProjectiveDescent

/-!
# Coefficient structures of the original conic and initial fiber descents

The complete affine branch cover and the incidence-conic pushout detect the base equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)

/-- The entire first conic parameter preserves coefficients. -/
@[reassoc] theorem conicFirstParameter_structure :
    (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫
      conicStructure a c =
        Spec.map (CommRingCat.ofHom (algebraMap K (ConicParameterOpen c))) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicFirstOpen a c))]
  exact terminalComponent_algebra_structure (conicFirstParameterEquiv a c ha).symm.toAlgHom

/-- The entire opposite conic parameter preserves coefficients. -/
@[reassoc] theorem conicSecondParameter_structure :
    (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫
      conicStructure a c =
        Spec.map (CommRingCat.ofHom (algebraMap K (ConicParameterOpen c))) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicSecondOpen a c))]
  exact terminalComponent_algebra_structure (conicSecondParameterEquiv a c ha).symm.toAlgHom

variable (hc : c = 0) {Y : Scheme.{u}} (f₁ f₂ : ProjectiveLine.scheme K ⟶ Y)
  (p : Y ⟶ Spec (.of K))
  (hf₁ : f₁ ≫ p = ProjectiveLine.toBase K) (hf₂ : f₂ ≫ p = ProjectiveLine.toBase K)

include hf₁ hf₂ in
/-- Descent from both full original branch components preserves their coefficient field. -/
theorem conicZeroProjectiveDesc_structure :
    conicZeroProjectiveDesc a c ha hc f₁ f₂ ≫ p = conicStructure a c := by
  apply conicParameter_hom_ext a c ha
  · apply (cancel_epi (conicZeroAffineIso c hc).hom).mp
    simp only [Category.assoc]
    rw [conicZeroProjectiveDesc_first_assoc, hf₁, ProjectiveLine.left_toBase,
      conicFirstParameter_structure, conicZeroAffineIso_structure]
  · apply (cancel_epi (conicZeroAffineIso c hc).hom).mp
    simp only [Category.assoc]
    rw [conicZeroProjectiveDesc_second_assoc, hf₂, ProjectiveLine.left_toBase,
      conicSecondParameter_structure, conicZeroAffineIso_structure]

variable (b : Kˣ) (g : ProjectiveLine.scheme K ⟶ Y)
  (w₁ : ProjectiveLine.zero K ≫ f₁ = ProjectiveLine.zero K ≫ g)
  (w₂ : ProjectiveLine.zero K ≫ f₂ = ProjectiveLine.infinity K ≫ g)
  (hg : g ≫ p = ProjectiveLine.toBase K)

include hf₁ hf₂ hg in
/-- The whole initial fiber descent is a morphism over the original coefficient field. -/
theorem fullFiberProjectiveDesc_structure :
    fullFiberProjectiveDesc b c hc f₁ f₂ g w₁ w₂ ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap K (FiberCoordinate (b : K) c))) := by
  apply fullFiber_components_hom_ext (b : K) c b.isUnit
  · rw [fullFiberProjectiveDesc_incidence_assoc, hg,
      ProjectiveLine.slopeNormalizationIso_base, ProjectiveLine.left_toBase]
    exact (terminalComponent_algebra_structure (fiberIncidenceMap (b : K) c)).symm
  · rw [fullFiberProjectiveDesc, fullFiberMarkedDesc_conic_assoc]
    have H := conicZeroProjectiveDesc_structure (b : K) c b.isUnit hc f₁ f₂ p hf₁ hf₂
    rw [conicZeroProjectiveDesc] at H
    rw [H]
    exact (terminalComponent_algebra_structure (fiberConicMap (b : K) c)).symm

end FLT.Mazur.WeierstrassModificationX

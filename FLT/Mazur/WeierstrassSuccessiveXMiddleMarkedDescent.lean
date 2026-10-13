/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleFiberDescent
public import FLT.Mazur.WeierstrassModificationXConicParameterSections

/-!
# Full middle-fiber descent using the original conic markings

The negated second parameter preserves its actual origin. Both compatibility
conditions can therefore be stated directly at the original conic incidence points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (c : K)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
  {Y : Scheme.{u}} (f : Spec (.of (ConicCoordinate W.a₁ c)) ⟶ Y)
  (g₁ g₂ : ProjectiveLine.chart K ⟶ Y)
  (w₁ : Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint W.a₁ c ha).toRingHom) ≫ f =
    ProjectiveLine.chartZero K ≫ g₁)
  (w₂ : Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint W.a₁ c ha).toRingHom) ≫ f =
    ProjectiveLine.chartZero K ≫ g₂)
local notation "o" => Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom)
local notation "p₁" => (conicFirstParameterIso W.a₁ c ha).inv ≫
  conicFirstOpenImmersion W.a₁ c
local notation "p₂" => Spec.map (CommRingCat.ofHom (conicParameterNeg c).toRingHom) ≫
  (conicSecondParameterIso W.a₁ c ha).inv ≫ conicSecondOpenImmersion W.a₁ c

include w₁ in
/-- The first original conic marking supplies the first full middle-node compatibility. -/
theorem middleMarked_first_compatible : o ≫ p₁ ≫ f = ProjectiveLine.chartZero K ≫ g₁ := by
  simpa only [Category.assoc, conicFirstParameterIso_origin_assoc] using w₁

include w₂ in
/-- The original opposite marking also supplies compatibility after parameter negation. -/
theorem middleMarked_second_compatible : o ≫ p₂ ≫ f = ProjectiveLine.chartZero K ≫ g₂ := by
  simp only [Category.assoc]
  erw [middleParameterNeg_origin_assoc, conicSecondParameterIso_origin_assoc]
  exact w₂

/-- Original marked component maps descend on the entire retained middle equation. -/
@[irreducible] def middleMarkedDesc : Spec (.of (Coordinate W 0 0 0 0 c)) ⟶ Y :=
  middleFiberDesc W c h2 ha f g₁ g₂
    (middleMarked_first_compatible W c ha f g₁ w₁)
    (middleMarked_second_compatible W c ha f g₂ w₂)

/-- The constructed map retains the full conic at the original divided constant. -/
@[reassoc] theorem middleMarkedDesc_conic :
    middleConicImmersion W c h2 ≫ middleMarkedDesc W c h2 ha f g₁ g₂ w₁ w₂ = f := by
  rw [middleMarkedDesc, middleFiberDesc_conic]

/-- The first full horizontal line retains its prescribed map. -/
@[reassoc] theorem middleMarkedDesc_first :
    middleLineImmersion W c h2 0 (middle_first_root W) ≫
      middleMarkedDesc W c h2 ha f g₁ g₂ w₁ w₂ = g₁ := by
  rw [middleMarkedDesc, middleFiberDesc_firstLine]

/-- The opposite full horizontal line retains its independently prescribed map. -/
@[reassoc] theorem middleMarkedDesc_second :
    middleLineImmersion W c h2 (-W.a₁) (middle_second_root W) ≫
      middleMarkedDesc W c h2 ha f g₁ g₂ w₁ w₂ = g₂ := by
  rw [middleMarkedDesc, middleFiberDesc_secondLine]

end FLT.Mazur.WeierstrassSuccessiveX

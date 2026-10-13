/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullFiberDescent
public import FLT.Mazur.WeierstrassModificationXConicParameterSections
public import FLT.Mazur.WeierstrassModificationXFullNodeProjectiveDescent

/-!
# Full incidence-conic descent from the two actual markings

Replace localized node compatibility by equality at the original conic
markings and the slope values zero and minus the tangent coefficient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
  {Y : Scheme.{u}} (f : Spec (.of (ConicCoordinate a c)) ⟶ Y)
  (g : ProjectiveLine.chart K ⟶ Y)
  (w₁ : Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫ f =
    ProjectiveLine.chartZero K ≫ g)
  (w₂ : Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫ f =
    Spec.map (CommRingCat.ofHom (aeval (-a) : K[X] →ₐ[K] K).toRingHom) ≫ g)
local notation "s₁" => fullNodeNormalizedDenominator a c
local notation "s₂" => fullNodeNormalizedDenominator (-a) c
local notation "hs₁" => fullNodeNormalizedDenominator_value a c ha
local notation "hs₂" => fullNodeNormalizedDenominator_value (-a) c ha.neg
local notation "o" => Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom)

include w₁ in
/-- The first marking gives exactly the full first node's origin compatibility. -/
theorem fullFiberMarked_first_compatible :
    o ≫ (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫ f =
      NodeLocalDescent.secondOrigin K s₁ hs₁ ≫
        NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₁) ≫ g := by
  rw [conicFirstParameterIso_origin_assoc, NodeLocalDescent.secondOrigin_branchOpen_assoc]
  exact w₁

include w₂ in
/-- The opposite marking retains the negative slope translation on the full second node. -/
theorem fullFiberMarked_second_compatible :
    o ≫ (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫ f =
      NodeLocalDescent.secondOrigin K s₂ hs₂ ≫
        NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₂) ≫
          Spec.map (CommRingCat.ofHom (aeval (X - C a) : K[X] →ₐ[K] K[X]).toRingHom) ≫ g := by
  rw [conicSecondParameterIso_origin_assoc, NodeLocalDescent.secondOrigin_branchOpen_assoc]
  have ht := fullNode_translatedParameter_origin_assoc (Units.mk0 a ha.ne_zero) g
  simp only [Units.val_mk0] at ht
  rw [ht]
  exact w₂

/-- The actual marked conic and full incidence line descend at any divided constant. -/
@[irreducible] def fullFiberMarkedDesc : Spec (.of (FiberCoordinate a c)) ⟶ Y :=
  fullFiberDesc a c ha f g (fullFiberMarked_first_compatible a c ha f g w₁)
    (fullFiberMarked_second_compatible a c ha f g w₂)

/-- The descended map restricts to the given entire conic. -/
@[reassoc] theorem fullFiberMarkedDesc_conic :
    fiberConicImmersion a c ≫ fullFiberMarkedDesc a c ha f g w₁ w₂ = f := by
  rw [fullFiberMarkedDesc, fullFiberDesc_conic]

/-- The descended map restricts to the given entire slope line. -/
@[reassoc] theorem fullFiberMarkedDesc_incidence :
    fiberIncidenceImmersion a c ≫ fullFiberMarkedDesc a c ha f g w₁ w₂ = g := by
  rw [fullFiberMarkedDesc, fullFiberDesc_incidence]

include w₁ w₂ in
/-- The two original marked compatibilities suffice for the full fiber universal property. -/
theorem fullFiberMarked_exists_unique_desc :
    ∃! d : Spec (.of (FiberCoordinate a c)) ⟶ Y,
      fiberConicImmersion a c ≫ d = f ∧ fiberIncidenceImmersion a c ≫ d = g :=
  fullFiber_exists_unique_desc a c ha f g
    (fullFiberMarked_first_compatible a c ha f g w₁)
    (fullFiberMarked_second_compatible a c ha f g w₂)

end FLT.Mazur.WeierstrassModificationX

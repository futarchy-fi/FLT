/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullFiberMarkedDescent
public import FLT.Mazur.WeierstrassConicZeroDescent
public import FLT.Mazur.WeierstrassConicZeroAffineParameter

/-!
# Initial full-fiber descent from the original three projective components

The two full affine branches of the zero-constant conic and the entire slope
line descend using only the two exterior-to-branch endpoint compatibilities.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (a : Kˣ) (c : K) (hc : c = 0)
local notation "ha" => a.isUnit
local notation "Z" => conicZeroAffineIso c hc
local notation "p₁" => (conicFirstParameterIso (a : K) c ha).inv ≫
  conicFirstOpenImmersion (a : K) c
local notation "p₂" => (conicSecondParameterIso (a : K) c ha).inv ≫
  conicSecondOpenImmersion (a : K) c
variable {Y : Scheme.{u}} (f₁ f₂ g : ProjectiveLine.scheme K ⟶ Y)
local notation "C₀" => conicZeroDesc (a : K) c ha hc
  ((Z).inv ≫ ProjectiveLine.left K ≫ f₁) ((Z).inv ≫ ProjectiveLine.left K ≫ f₂)
local notation "L" => ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ g

/-- The actual first conic incidence marking is zero of the first complete branch. -/
@[reassoc] theorem fullFiberProjectiveConic_first_origin :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (a : K) c ha).toRingHom) ≫ C₀ =
      ProjectiveLine.zero K ≫ f₁ := by
  rw [← conicFirstParameterIso_origin_assoc, ← Category.assoc _ _ C₀,
    conicZeroDesc_first, ← conicZeroAffineIso_origin c hc, Category.assoc,
    Iso.hom_inv_id_assoc]
  rfl

/-- The opposite conic marking is zero of the independent opposite complete branch. -/
@[reassoc] theorem fullFiberProjectiveConic_second_origin :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (a : K) c ha).toRingHom) ≫ C₀ =
      ProjectiveLine.zero K ≫ f₂ := by
  rw [← conicSecondParameterIso_origin_assoc, ← Category.assoc _ _ C₀,
    conicZeroDesc_second, ← conicZeroAffineIso_origin c hc, Category.assoc,
    Iso.hom_inv_id_assoc]
  rfl

variable
  (w₁ : ProjectiveLine.zero K ≫ f₁ = ProjectiveLine.zero K ≫ g)
  (w₂ : ProjectiveLine.zero K ≫ f₂ = ProjectiveLine.infinity K ≫ g)

include w₁ in
/-- Exterior zero supplies the first actual incidence-conic compatibility. -/
theorem fullFiberProjective_first_compatible :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint (a : K) c ha).toRingHom) ≫ C₀ =
      ProjectiveLine.chartZero K ≫ L := by
  rw [fullFiberProjectiveConic_first_origin]
  exact w₁.trans (ProjectiveLine.slopeNormalization_first_assoc a g).symm

include w₂ in
/-- Exterior infinity supplies the opposite compatibility with the original negative slope. -/
theorem fullFiberProjective_second_compatible :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint (a : K) c ha).toRingHom) ≫ C₀ =
      Spec.map (CommRingCat.ofHom (aeval (-(a : K)) : K[X] →ₐ[K] K).toRingHom) ≫ L := by
  rw [fullFiberProjectiveConic_second_origin]
  exact w₂.trans (ProjectiveLine.slopeNormalization_second_assoc a g).symm

/-- The entire initial equation receives maps from the original complete components. -/
@[irreducible] def fullFiberProjectiveDesc : Spec (.of (FiberCoordinate (a : K) c)) ⟶ Y :=
  fullFiberMarkedDesc (a : K) c ha C₀ L
    (fullFiberProjective_first_compatible a c hc f₁ f₂ g w₁)
    (fullFiberProjective_second_compatible a c hc f₁ f₂ g w₂)

/-- The first complete affine branch restriction is retained. -/
@[reassoc] theorem fullFiberProjectiveDesc_first :
    (Z).hom ≫ p₁ ≫ fiberConicImmersion (a : K) c ≫
      fullFiberProjectiveDesc a c hc f₁ f₂ g w₁ w₂ = ProjectiveLine.left K ≫ f₁ := by
  rw [fullFiberProjectiveDesc, fullFiberMarkedDesc_conic,
    conicZeroDesc_first, Iso.hom_inv_id_assoc]

/-- The opposite complete affine branch restriction is retained. -/
@[reassoc] theorem fullFiberProjectiveDesc_second :
    (Z).hom ≫ p₂ ≫ fiberConicImmersion (a : K) c ≫
      fullFiberProjectiveDesc a c hc f₁ f₂ g w₁ w₂ = ProjectiveLine.left K ≫ f₂ := by
  rw [fullFiberProjectiveDesc, fullFiberMarkedDesc_conic,
    conicZeroDesc_second, Iso.hom_inv_id_assoc]

/-- The entire original slope line is the actual normalized exterior restriction. -/
@[reassoc] theorem fullFiberProjectiveDesc_incidence :
    fiberIncidenceImmersion (a : K) c ≫ fullFiberProjectiveDesc a c hc f₁ f₂ g w₁ w₂ = L := by
  rw [fullFiberProjectiveDesc, fullFiberMarkedDesc_incidence]

end FLT.Mazur.WeierstrassModificationX

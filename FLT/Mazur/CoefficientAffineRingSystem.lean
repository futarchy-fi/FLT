/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelFiniteness
public import FLT.Mazur.PointLocalizedRingColimit

/-!
# Coordinate rings of actual affine coefficient model stages

Take an affine chart of the finite model and its actual coefficient pullbacks.
Their coordinate rings form a filtered system recovering the original-base
pullback. At every chosen point, its local coordinate rings also recover the
original local ring and are Noetherian at finite stages.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CoefficientAffineRingSystem
open Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A : Type u} [CommRing A] (R : Subalgebra ℤ A)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) [IsAffine Y]

/-- The actual affine scheme at a coefficient stage. -/
abbrev Model (i : CoefficientStage R) := (coefficientModelDiagram R q).obj (.op i)

instance model_isAffine (i : CoefficientStage R) : IsAffine (Model R q i) := by
  change IsAffine (pullback q (Spec.map
    (CommRingCat.ofHom (Subalgebra.inclusion i.property.1).toRingHom)))
  infer_instance

/-- Global sections of the actual affine coefficient pullbacks, with their actual maps. -/
def diagram : CoefficientStage R ⥤ CommRingCat.{u} :=
  opOp (CoefficientStage R) ⋙ (coefficientModelDiagram R q).op ⋙ Scheme.Γ

/-- The coordinate ring of the pullback to the original affine base is the cocone vertex. -/
def cocone : Cocone (diagram R q) :=
  (Scheme.Γ.mapCocone (coefficientModelCone R q).op).whisker (opOp (CoefficientStage R))

/-- Finite-type affine coefficient models have Noetherian coordinate rings. -/
instance stage_noetherian [LocallyOfFiniteType q] (i : CoefficientStage R) :
    IsNoetherianRing ((diagram R q).obj i) := by
  let _ : IsNoetherian (Model R q i) := coefficientModel_isNoetherian q (.op i)
  change IsNoetherianRing Γ(Model R q i, ⊤)
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The actual affine model coordinate rings recover the original-base coordinate ring. -/
def isColimit [Algebra.FiniteType ℤ R] : IsColimit (cocone R q) := by
  let _ (i : (CoefficientStage R)ᵒᵖ) :
      IsAffine ((coefficientModelDiagram R q).obj i) := model_isAffine R q i.unop
  refine (Functor.Final.isColimitWhiskerEquiv (opOp (CoefficientStage R))
    (Scheme.Γ.mapCocone (coefficientModelCone R q).op)).symm ?_
  exact (nonempty_isColimit_Γ_mapCocone (coefficientModelDiagram R q)
    (coefficientModelCone R q) (coefficientModelIsLimit R q)).some

variable (P : Ideal (cocone R q).pt) [P.IsPrime]

/-- The target local ring at a point's image in the actual affine coefficient model. -/
abbrev LocalRing (i : CoefficientStage R) :=
  PointLocalizedRingDiagram.Stage (cocone R q) P i

instance localRing_noetherian [LocallyOfFiniteType q] (i : CoefficientStage R) :
    IsNoetherianRing (LocalRing R q P i) :=
  PointLocalizedRingDiagram.stage_noetherian (cocone R q) P i

/-- Local target rings of the actual affine coefficient models recover the original local ring. -/
def localIsColimit [Algebra.FiniteType ℤ R] :
    IsColimit (PointLocalizedRingDiagram.cocone (cocone R q) P) :=
  PointLocalizedRingDiagram.localizedIsColimit (cocone R q) P (isColimit R q)

end FLT.Mazur.CoefficientAffineRingSystem

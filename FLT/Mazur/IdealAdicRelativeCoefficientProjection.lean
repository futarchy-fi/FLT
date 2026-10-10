/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientDescent

/-!
# Compatibility of descended coefficient projections

Canonical projections to the original tensor-chart pushforwards respect
the original overlap comparisons and the actual chart scalar action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur

/-- Cancel the target change of coordinates in a conjugated comparison square. -/
lemma projection_conjugate {C : Type*} [Category C] {M A B P Q : C}
    (p : M ⟶ A) (q : M ⟶ B) (a : A ≅ P) (b : B ≅ Q) (t : P ≅ Q)
    (h : p ≫ (a ≪≫ t ≪≫ b.symm).hom = q) :
    (p ≫ a.hom) ≫ t.hom = q ≫ b.hom := by
  have h' := congrArg (fun k ↦ k ≫ b.hom) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using h'

namespace IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] Scheme.Modules.pullback relativeChartCoefficientSheaf
attribute [local irreducible] relativeImageCoefficientPushforwardIso

/-- Descended projections obey the original ambient chart transition on every overlap. -/
lemma relativeDescendedCoefficientProjection_transition (U V : X.affineOpens) :
    (relativeDescendedCoefficientProjection J f U).over
        (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V) ≫
      (relativeChartCoefficientImageTransition J f U V).hom =
    (relativeDescendedCoefficientProjection J f V).over
      (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V) := by
  unfold relativeDescendedCoefficientProjection
  let F := SheafOfModules.overFunctor (relativeScheme J f).ringCatSheaf
    (relativeTensorImageOpen J f U ⊓ relativeTensorImageOpen J f V)
  change (F.map ((relativeCoefficientGluingData J f).projection U) ≫
      (F.mapIso (relativeImageCoefficientPushforwardIso J f U)).hom) ≫
        (relativeChartCoefficientImageTransition J f U V).hom =
    F.map ((relativeCoefficientGluingData J f).projection V) ≫
      (F.mapIso (relativeImageCoefficientPushforwardIso J f V)).hom
  exact projection_conjugate _ _ _ _ _
    ((relativeCoefficientGluingData J f).projection_transition U V)

/-- Ambient scalars act through their actual pullback to the original tensor chart. -/
lemma relativeDescendedCoefficientProjection_smul (U : X.affineOpens)
    (W : (relativeScheme J f).Opens) (r : Γ(relativeScheme J f, W))
    (s : Γ(relativeDescendedCoefficientSheaf J f, W)) :
    (relativeDescendedCoefficientProjection J f U).app W (r • s) =
      ((relativeChartCoefficientSheaf J f U).smul
        (U := relativeTensorChart J f U ⁻¹ᵁ W) ((relativeTensorChart J f U).app W r)).hom
        ((relativeDescendedCoefficientProjection J f U).app W s) :=
  (relativeDescendedCoefficientProjection J f U).app_smul r s

end IdealAdicGradedPullback

end FLT.Mazur

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeScheme

/-!
# Original tensor rings as charts of the changed-base scheme

The spectrum of the original relative tensor ring is the pullback over
an actual closed affine chart. The resulting chart morphism is an open
immersion, and both projections retain their original ring maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections
open scoped TensorProduct

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y) (U : X.affineOpens)

omit [IsLocallyNoetherian Y] in
/-- The closed chart retains the original closed scalar map to the affine base. -/
lemma closedAffineChart_base :
    (closedAffineChart J f U).2.fromSpec ≫ closedSourceBaseMap J f =
      Spec.map (CommRingCat.ofHom (closedBaseMap J f U.1)) := by
  change (closedAffineChart J f U).2.fromSpec ≫
    ((J.comap f).subschemeι ≫ f) ≫ Y.toSpecΓ = _
  rw [Scheme.toSpecΓ_naturality, IsAffineOpen.fromSpec_toSpecΓ_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (closedBaseMap_eq_source J f U.1).symm

/-- The original relative tensor spectrum maps to the actual graded base by its left factor. -/
def relativeTensorToBase :
    let := closedBaseAlgebra J f U.1
    Spec (.of (RelativeAlgebra J f U)) ⟶ gradedBaseScheme J := by
  let := closedBaseAlgebra J f U.1
  exact Spec.map (CommRingCat.ofHom (algebraMap
    (IdealAdicGradedSections.Sections J ⊤) (RelativeAlgebra J f U)))

/-- The original relative tensor spectrum maps to the actual closed chart by its right factor. -/
def relativeTensorToChart :
    let := closedBaseAlgebra J f U.1
    Spec (.of (RelativeAlgebra J f U)) ⟶ Spec (ClosedScalars (J.comap f) U.1) := by
  let := closedBaseAlgebra J f U.1
  exact Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := Γ(Y, ⊤))
      (A := IdealAdicGradedSections.Sections J ⊤)
      (B := ClosedScalars (J.comap f) U.1)).toRingHom)

/-- The original tensor spectrum is the Cartesian product over the affine coordinate base. -/
lemma relativeTensor_isPullback :
    let := closedBaseAlgebra J f U.1
    IsPullback (relativeTensorToBase J f U) (relativeTensorToChart J f U)
      (gradedBaseMap J) ((closedAffineChart J f U).2.fromSpec ≫ closedSourceBaseMap J f) := by
  let := closedBaseAlgebra J f U.1
  rw [closedAffineChart_base]
  let e := pullbackSpecIso Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)
    (ClosedScalars (J.comap f) U.1)
  have h₁ : e.inv ≫ pullback.fst _ _ = relativeTensorToBase J f U :=
    pullbackSpecIso_inv_fst' _ _ _
  have h₂ : e.inv ≫ pullback.snd _ _ = relativeTensorToChart J f U :=
    pullbackSpecIso_inv_snd _ _ _
  apply IsPullback.of_iso_pullback _ e.symm h₁ h₂
  exact ⟨by rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]⟩

/-- The tensor chart maps into the changed-base scheme by its Cartesian universal property. -/
def relativeTensorChart :
    let := closedBaseAlgebra J f U.1
    Spec (.of (RelativeAlgebra J f U)) ⟶ relativeScheme J f := by
  let := closedBaseAlgebra J f U.1
  exact (relativeScheme_isPullback J f).lift (relativeTensorToBase J f U)
    (relativeTensorToChart J f U ≫ (closedAffineChart J f U).2.fromSpec)
    (by rw [Category.assoc]; exact (relativeTensor_isPullback J f U).w)

/-- The chart map preserves the original graded-base projection. -/
@[reassoc]
lemma relativeTensorChart_toBase :
    let := closedBaseAlgebra J f U.1
    relativeTensorChart J f U ≫ relativeSchemeToBase J f = relativeTensorToBase J f U := by
  let := closedBaseAlgebra J f U.1
  exact (relativeScheme_isPullback J f).lift_fst _ _ _

/-- The chart map preserves the original closed-source projection. -/
@[reassoc]
lemma relativeTensorChart_toClosed :
    let := closedBaseAlgebra J f U.1
    relativeTensorChart J f U ≫ relativeSchemeToClosed J f =
      relativeTensorToChart J f U ≫ (closedAffineChart J f U).2.fromSpec := by
  let := closedBaseAlgebra J f U.1
  exact (relativeScheme_isPullback J f).lift_snd _ _ _

/-- This is the actual inverse image of the chosen closed affine chart. -/
lemma relativeTensorChart_isPullback :
    let := closedBaseAlgebra J f U.1
    IsPullback (relativeTensorChart J f U) (relativeTensorToChart J f U)
      (relativeSchemeToClosed J f) (closedAffineChart J f U).2.fromSpec := by
  let := closedBaseAlgebra J f U.1
  exact (relativeTensor_isPullback J f U).of_right' (relativeScheme_isPullback J f)

/-- Every original tensor chart is an open immersion into the actual changed-base scheme. -/
lemma relativeTensorChart_isOpenImmersion :
    let := closedBaseAlgebra J f U.1
    IsOpenImmersion (relativeTensorChart J f U) := by
  let := closedBaseAlgebra J f U.1
  exact IsOpenImmersion.of_isPullback (relativeTensorChart_isPullback J f U).flip
    inferInstance

end FLT.Mazur.IdealAdicGradedPullback

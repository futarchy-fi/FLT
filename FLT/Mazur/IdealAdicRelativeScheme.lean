/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeNoetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The scheme obtained by changing to the actual graded base algebra

The construction is a scheme pullback of the actual closed source along
the spectrum of the actual graded base algebra. Its projection to the
closed source is affine and finitely presented; properness over the new
base follows from properness of the original morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.IdealAdicGradedSections

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData)

/-- The spectrum of the actual total graded algebra of the affine base. -/
def gradedBaseScheme : Scheme.{u} :=
  Spec (.of (IdealAdicGradedSections.Sections J ⊤))

/-- The original algebra scalar map gives the change of affine base. -/
def gradedBaseMap : gradedBaseScheme J ⟶ Spec Γ(Y, ⊤) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)))

instance gradedBaseScheme_isLocallyNoetherian : IsLocallyNoetherian (gradedBaseScheme J) := by
  let _ := affineSections_isNoetherianRing J ⟨⊤, isAffineOpen_top _⟩
  exact inferInstanceAs (IsLocallyNoetherian
    (Spec (.of (IdealAdicGradedSections.Sections J ⊤))))

instance gradedBaseMap_locallyOfFiniteType : LocallyOfFiniteType (gradedBaseMap J) := by
  let _ := affineSections_finiteType J ⟨⊤, isAffineOpen_top _⟩
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  exact RingHom.finiteType_algebraMap.mpr
    (inferInstanceAs (Algebra.FiniteType Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)))

instance gradedBaseMap_isAffineHom : IsAffineHom (gradedBaseMap J) :=
  inferInstanceAs (IsAffineHom (Spec.map _))

variable (f : X ⟶ Y)

/-- The actual closed source maps to the original affine coordinate spectrum. -/
def closedSourceBaseMap : (J.comap f).subscheme ⟶ Spec Γ(Y, ⊤) :=
  (J.comap f).subschemeι ≫ f ≫ Y.toSpecΓ

/-- Change the actual closed scheme to the actual graded coefficient base. -/
def relativeScheme : Scheme.{u} := pullback (gradedBaseMap J) (closedSourceBaseMap J f)

/-- The projection to the graded affine base. -/
def relativeSchemeToBase : relativeScheme J f ⟶ gradedBaseScheme J :=
  pullback.fst _ _

/-- The projection to the original closed source. -/
def relativeSchemeToClosed : relativeScheme J f ⟶ (J.comap f).subscheme :=
  pullback.snd _ _

omit [IsAffine Y] in
/-- The actual structural maps form the defining Cartesian square. -/
lemma relativeScheme_isPullback :
    IsPullback (relativeSchemeToBase J f) (relativeSchemeToClosed J f)
      (gradedBaseMap J) (closedSourceBaseMap J f) := IsPullback.of_hasPullback _ _

instance relativeSchemeToClosed_isAffineHom : IsAffineHom (relativeSchemeToClosed J f) := by
  exact MorphismProperty.of_isPullback (relativeScheme_isPullback J f)
    (gradedBaseMap_isAffineHom J)

instance relativeSchemeToClosed_locallyOfFiniteType :
    LocallyOfFiniteType (relativeSchemeToClosed J f) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))

variable [IsLocallyNoetherian X]

instance relativeScheme_isLocallyNoetherian : IsLocallyNoetherian (relativeScheme J f) := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian (J.comap f).subschemeι
  exact inferInstanceAs
    (IsLocallyNoetherian (pullback (gradedBaseMap J) (closedSourceBaseMap J f)))

instance relativeSchemeToClosed_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (relativeSchemeToClosed J f) := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian (J.comap f).subschemeι
  infer_instance

omit [IsLocallyNoetherian X] in
/-- Properness of the original morphism survives closing the source and changing the base. -/
instance relativeSchemeToBase_isProper [IsProper f] : IsProper (relativeSchemeToBase J f) := by
  let _ : IsProper (closedSourceBaseMap J f) :=
    inferInstanceAs (IsProper ((J.comap f).subschemeι ≫ f ≫ Y.toSpecΓ))
  exact inferInstanceAs (IsProper (pullback.fst _ _))

end FLT.Mazur.IdealAdicGradedPullback

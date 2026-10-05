/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicClosedGradedModule
public import FLT.Mazur.IdealAdicClosedScalar

/-!
# Restriction of the actual total graded coefficients

The section rings form a presheaf, and the actual base comparison commutes
with restriction. This is a presheaf assertion: an infinite direct sum of
section sheaves still requires sheafification on arbitrary opens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- Identity restriction fixes every actual total graded section. -/
lemma restrict_id (U : X.Opens) : restrictRingHom I U (𝟙 U) = RingHom.id _ := by
  apply DirectSum.ringHom_ext
  intro n s
  change restrict I U (𝟙 U) (of I U n s) = of I U n s
  rw [restrict_of]
  congr 1
  exact ConcreteCategory.congr_hom ((idealGraded I n).presheaf.map_id (.op U)) s

/-- The actual graded restrictions compose. -/
lemma restrict_comp {U V W : X.Opens} (i : U ⟶ V) (j : V ⟶ W) :
    (restrictRingHom I U i).comp (restrictRingHom I V j) =
      restrictRingHom I U (i ≫ j) := by
  apply DirectSum.ringHom_ext
  intro n s
  change restrict I U i (restrict I V j (of I W n s)) =
    restrict I U (i ≫ j) (of I W n s)
  rw [restrict_of, restrict_of, restrict_of]
  congr 1
  exact (ConcreteCategory.congr_hom
    ((idealGraded I n).presheaf.map_comp j.op i.op) s).symm

/-- The actual direct sums and their ring restrictions form a presheaf. -/
def ringPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (Sections I U.unop)
  map i := CommRingCat.ofHom (restrictRingHom I _ i.unop)
  map_id U := congrArg CommRingCat.ofHom (restrict_id I U.unop)
  map_comp i j := (congrArg CommRingCat.ofHom (restrict_comp I j.unop i.unop)).symm

/-- Closed coordinate restriction is the actual structure-sheaf restriction. -/
def closedScalarRestriction {U V : X.Opens} (i : U ⟶ V) :
    ClosedScalars I V →+* ClosedScalars I U :=
  (I.subscheme.presheaf.map ((TopologicalSpace.Opens.map I.subschemeι.base).map i).op).hom

/-- Closed scalar inclusion commutes with restriction on arbitrary ambient opens. -/
lemma closedScalarAdd_restrict {U V : X.Opens} (i : U ⟶ V) (r : ClosedScalars I V) :
    restrict I U i (closedScalarAdd I V r) =
      closedScalarAdd I U (closedScalarRestriction I i r) := by
  change restrict I U i (of I V 0 ((zeroSectionEquiv I V).symm r)) =
    of I U 0 ((zeroSectionEquiv I U).symm (closedScalarRestriction I i r))
  rw [restrict_of]
  congr 1
  exact (PresheafOfModules.naturality_apply (idealGradedZeroIso I).inv.val i.op r).symm

end FLT.Mazur.IdealAdicGradedSections

namespace FLT.Mazur.IdealAdicGradedPullback

open FLT.Mazur.IdealAdicGradedSections

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y] in
/-- The actual homogeneous base generators commute with source restriction. -/
lemma gradedSection_restrict {U V : X.Opens} (i : U ⟶ V) (n : ℕ) (s : Piece J ⊤ n) :
    (idealGraded (J.comap f) n).presheaf.map i.op (gradedSection J f n V s) =
      gradedSection J f n U s := by
  unfold gradedSection
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The local maps from the actual base algebra commute with restriction. -/
lemma localRingHom_restrict {U V : X.Opens} (i : U ⟶ V) :
    (restrictRingHom (J.comap f) U i).comp (localRingHom J f V) =
      localRingHom J f U := by
  apply DirectSum.ringHom_ext
  intro n s
  change restrict (J.comap f) U i (localRingHom J f V (of J ⊤ n s)) =
    localRingHom J f U (of J ⊤ n s)
  rw [localRingHom_of, restrict_of, gradedSection_restrict, localRingHom_of]

/-- Restriction is linear over the fixed actual base graded algebra. -/
def baseRestriction {U V : X.Opens} (i : U ⟶ V) :
    let := localBaseAlgebra J f V
    let := localBaseAlgebra J f U
    IdealAdicGradedSections.Sections (J.comap f) V →ₗ[IdealAdicGradedSections.Sections J ⊤]
      IdealAdicGradedSections.Sections (J.comap f) U := by
  let := localBaseAlgebra J f V
  let := localBaseAlgebra J f U
  refine { restrict (J.comap f) U i with map_smul' := ?_ }
  intro r s
  change restrictRingHom (J.comap f) U i (localRingHom J f V r * s) =
    localRingHom J f U r * restrictRingHom (J.comap f) U i s
  rw [map_mul]
  congr 1
  exact RingHom.congr_fun (localRingHom_restrict J f i) r

end FLT.Mazur.IdealAdicGradedPullback

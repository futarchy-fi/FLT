/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjBaseChangeProjection
public import FLT.Mazur.SectionGradedProjNaturality

/-!
# Cartesian base change of canonical section-ring Proj maps

The section-algebra comparison identifies the actual canonical morphisms.
Pasting with the intrinsic structural square proves their square Cartesian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjCanonicalSquare
open FCurve SectionGradedSum SectionGradedBaseChange SectionGradedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- Pullback preserves the line-bundle condition. -/
local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩

/-- The projection expressed in the structure-sheaf grading on both sides. -/
def projection : Proj (grade ((pullback p).obj L) ⊤) ⟶ Proj (grade L ⊤) :=
  Proj.map (SectionGradedPullback.gradedRingHom p L)
    (SectionGradedProjBaseChangeProjection.irrelevant_le_map h L)

/-- The actual canonical source-to-Proj morphisms commute with flat base change. -/
@[reassoc]
lemma toProj_projection (hg : PositivePowerGenerated L) :
    toProj ((pullback p).obj L)
      (SectionGradedProjNaturality.positivePowerGenerated_pullback p L hg) ≫
      projection h L = p ≫ toProj L hg :=
  SectionGradedProjNaturality.toProj_map p L hg _

/-- The intrinsic structural Proj square in the structure-sheaf gradings is Cartesian. -/
lemma structural_isPullback :
    IsPullback (projection h L)
      (SectionGradedProjStructuralMap.toSpecBase q ((pullback p).obj L))
      (SectionGradedProjStructuralMap.toSpecBase f L) (Spec.map g.appTop) := by
  have hs := SectionGradedProjIntrinsicSquare.isPullback h L
  refine hs.of_iso (Iso.refl _) (SectionGradedProjGrading.iso f L).symm
    (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_ (by simp)
  · simpa [projection] using (SectionGradedProjBaseChangeProjection.projection_eq h L)
  · rw [← SectionGradedProjGrading.iso_toSpecBase f L]
    simp

/-- The square of actual canonical maps is Cartesian, with no assumed map compatibility. -/
lemma isPullback (hg : PositivePowerGenerated L) :
    IsPullback p
      (toProj ((pullback p).obj L)
        (SectionGradedProjNaturality.positivePowerGenerated_pullback p L hg))
      (toProj L hg) (projection h L) := by
  have ho : IsPullback p (q ≫ T.toSpecΓ) (f ≫ S.toSpecΓ) (Spec.map g.appTop) := by
    refine h.of_iso (Iso.refl _) (Iso.refl _)
      (asIso T.toSpecΓ) (asIso S.toSpecΓ) (by simp) (by simp) (by simp) ?_
    simpa using Scheme.toSpecΓ_naturality g
  have hs := structural_isPullback h L
  apply IsPullback.of_bot (t := hs) _ (toProj_projection h L hg).symm
  simpa only [SectionGradedProjStructuralMap.toProj_toSpecBase] using ho

end FLT.Mazur.SectionGradedProjCanonicalSquare

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjBaseChangeSquare
public import FLT.Mazur.SectionGradedProjGrading

/-!
# The intrinsic section-ring Proj base-change square

The transported structural map equals the intrinsic structural map of the
pulled-back section ring. Thus the established Cartesian square has its
actual structural morphism, without an extra compatibility hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjIntrinsicSquare
open FCurve SectionGradedSum SectionGradedBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- Pullback preserves the line-bundle condition. -/
local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩

/-- The algebra equivalence identifies the transported and intrinsic structural maps. -/
@[reassoc]
lemma iso_toSpecBase :
    (SectionGradedProjBaseChangeEquiv.iso h L).hom ≫
      GradedProjStructuralMap.toSpecBase (tensorGrade f L g) =
        SectionGradedProjStructuralMap.toSpecBase q ((pullback p).obj L) := by
  apply GradedProjStructuralNaturality.map_toSpecBase
    (tensorGrade f L g) (grade ((pullback p).obj L) ⊤) _ q.appTop.hom
  intro r
  change sectionsAlgEquiv h L hL.out (algebraMap Γ(T, ⊤) _ r) = _
  rw [(sectionsAlgEquiv h L hL.out).commutes, structural_algebraMap]
  rfl

/-- The structural map used in the transported square is the intrinsic one. -/
lemma toSpecBase_eq :
    SectionGradedProjBaseChangeSquare.toSpecBase h L =
      SectionGradedProjStructuralMap.toSpecBase q ((pullback p).obj L) :=
  iso_toSpecBase h L

/-- Flat base change of the section-ring Proj with its intrinsic structural map. -/
lemma isPullback :
    IsPullback (SectionGradedProjBaseChangeSquare.projection h L)
      (SectionGradedProjStructuralMap.toSpecBase q ((pullback p).obj L))
      (GradedProjStructuralMap.toSpecBase (baseGrade f L)) (Spec.map g.appTop) := by
  rw [← toSpecBase_eq h L]
  exact SectionGradedProjBaseChangeSquare.isPullback h L

end FLT.Mazur.SectionGradedProjIntrinsicSquare

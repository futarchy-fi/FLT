/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGradedProjBaseChange
public import FLT.Mazur.SectionGradedProjBaseChangeEquiv
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The section-ring Proj base-change square

The full section comparison identifies Proj of the pulled-back section ring
with the base change of the original structurally graded Proj.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjBaseChangeSquare
open FCurve SectionGradedSum SectionGradedBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- Pullback preserves the rank-one condition required for the commutative section ring. -/
local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩
/-- The section-algebra comparison followed by the Proj scalar-extension projection. -/
def projection : Proj (grade ((pullback p).obj L) ⊤) ⟶ Proj (baseGrade f L) := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact (SectionGradedProjBaseChangeEquiv.iso h L).hom ≫
    GradedProjBaseChangeMap.projection (B := Γ(T, ⊤)) (baseGrade f L)

/-- The structural map on the identified scalar-extended Proj. -/
def toSpecBase : Proj (grade ((pullback p).obj L) ⊤) ⟶ Spec Γ(T, ⊤) := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact (SectionGradedProjBaseChangeEquiv.iso h L).hom ≫
    GradedProjStructuralMap.toSpecBase
      (GradedProjBaseChangeMap.baseGrade (B := Γ(T, ⊤)) (baseGrade f L))

/-- The actual pulled-back section-ring Proj is the base change of the structural Proj. -/
lemma isPullback : IsPullback (projection h L) (toSpecBase h L)
    (GradedProjStructuralMap.toSpecBase (baseGrade f L)) (Spec.map g.appTop) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := RingHom.flat_algebraMap_iff.mp g.flat_appTop
  have hs := FlatGradedProjBaseChange.isPullback (B := Γ(T, ⊤)) (baseGrade f L)
  refine hs.of_iso (SectionGradedProjBaseChangeEquiv.iso h L).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) ?_
  · simp [projection]
  · simp [toSpecBase]
  · rfl

end FLT.Mazur.SectionGradedProjBaseChangeSquare

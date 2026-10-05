/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjRingEquiv
public import FLT.Mazur.SectionGradedBaseChangeGrading

/-!
# Proj comparison for the actual section algebra after base change

The full section-algebra equivalence carries the internal tensor grading to
the actual grading of the pulled-back line bundle. It therefore identifies
the two projective schemes, not just their underlying rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjBaseChangeEquiv
open FCurve SectionGradedSum SectionGradedBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- Pullback preserves the rank-one condition required for the commutative section ring. -/
local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩

/-- The full algebra equivalence preserves and reflects the actual internal tensor grading. -/
lemma sectionsAlgEquiv_mem_tensorGrade_iff (n : ℕ)
    (a : (ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) :
    sectionsAlgEquiv h L hL.out a ∈ grade ((pullback p).obj L) ⊤ n ↔
      a ∈ tensorGrade f L g n := by
  rw [tensorGrade_eq_extendedGrade]
  exact sectionsAlgEquiv_mem_grade_iff h L hL.out n a

/-- Proj of the pulled-back section ring is Proj of the internally graded scalar extension. -/
def iso : Proj (grade ((pullback p).obj L) ⊤) ≅ Proj (tensorGrade f L g) :=
  GradedProjRingEquiv.iso (tensorGrade f L g) (grade ((pullback p).obj L) ⊤)
    (sectionsAlgEquiv h L hL.out).toRingEquiv (sectionsAlgEquiv_mem_tensorGrade_iff h L)

/-- The comparison identifies basic opens through the actual full section-algebra map. -/
lemma iso_preimage_basicOpen
    (a : (ModuleCat.extendScalars g.appTop.hom).obj (sectionModule f L)) :
    (iso h L).hom ⁻¹ᵁ Proj.basicOpen (tensorGrade f L g) a =
      Proj.basicOpen (grade ((pullback p).obj L) ⊤) (sectionsAlgEquiv h L hL.out a) := rfl

end FLT.Mazur.SectionGradedProjBaseChangeEquiv

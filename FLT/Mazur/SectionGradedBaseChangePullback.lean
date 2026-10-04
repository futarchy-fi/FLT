/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjBaseChangeEquiv
public import FLT.Mazur.GradedProjBaseChangeMap
public import FLT.Mazur.SectionGradedPullbackRing

/-!
# The section-algebra comparison on original sections

The full section-algebra equivalence sends a section tensored with one to its
actual pullback. Consequently the composite graded map defining the Proj
projection is the original section-ring pullback, in every degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum ChangeOfRings TensorProduct
namespace FLT.Mazur.SectionGradedBaseChangePullback
open FCurve SectionGradedSum SectionGradedBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- Pullback preserves the line-bundle condition. -/
local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩

/-- On original homogeneous sections, the algebra comparison is actual section pullback. -/
lemma sectionsAlgEquiv_one_tmul_of (n : ℕ)
    (s : SectionGradedMultiplication.Piece L ⊤ n) :
    sectionsAlgEquiv h L hL.out ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] of L ⊤ n s) =
      of ((pullback p).obj L) ⊤ n (SectionGradedPullback.pull p L n ⊤ s) := by
  change (sectionsIso h L hL.out).hom _ = _
  rw [sectionsIso_tmul_of, LinePowerSectionBaseChange.degreeIso_tmul, one_smul]
  rfl

/-- On the whole original ring, tensoring with one followed by comparison is pullback. -/
lemma sectionsAlgEquiv_one_tmul (s : SectionGradedSum.Sections L ⊤) :
    sectionsAlgEquiv h L hL.out ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
      SectionGradedPullback.ringHom p L s := by
  induction s using DirectSum.induction_on with
  | zero => simp
  | of n s =>
    exact (sectionsAlgEquiv_one_tmul_of h L n s).trans
      (SectionGradedPullback.sumMap_of p L n s).symm
  | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]

/-- The scalar-extended graded map has exactly the actual pullback ring homomorphism. -/
lemma graded_comparison_comp_inclusion :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    (GradedProjRingEquiv.forward (tensorGrade f L g) (grade ((pullback p).obj L) ⊤)
      (sectionsAlgEquiv h L hL.out).toRingEquiv
      (SectionGradedProjBaseChangeEquiv.sectionsAlgEquiv_mem_tensorGrade_iff h L)).comp
        (GradedProjBaseChangeMap.inclusion (B := Γ(T, ⊤)) (baseGrade f L)) =
      (show baseGrade f L →+*ᵍ grade ((pullback p).obj L) ⊤ from
        { SectionGradedPullback.ringHom p L with
          map_mem := fun hs ↦ SectionGradedPullback.ringHom_mem_grade p L hs }) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  ext s : 1
  exact sectionsAlgEquiv_one_tmul h L s

end FLT.Mazur.SectionGradedBaseChangePullback

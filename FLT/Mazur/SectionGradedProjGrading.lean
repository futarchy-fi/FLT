/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjRingEquiv
public import FLT.Mazur.GradedProjStructuralNaturality
public import FLT.Mazur.GradedProjUnitChartMap
public import FLT.Mazur.SectionGradedProjStructuralMap

/-!
# Comparing the two scalar presentations of the section grading

The identity on the section ring identifies the structural grading and the
structure-sheaf grading. This identifies both structural and local Proj maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjGrading
open FCurve SectionGradedSum SectionGradedBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S : Scheme} (f : X ⟶ S) (L : X.Modules)
  [Fact (LocallyFreeRankOne L)]

/-- The two scalar presentations of the same graded ring have isomorphic Proj schemes. -/
def iso : Proj (grade L ⊤) ≅ Proj (baseGrade f L) :=
  GradedProjRingEquiv.iso (baseGrade f L) (grade L ⊤)
    (RingEquiv.refl _) (fun _ _ ↦ Iff.rfl)

/-- The identity-ring comparison preserves every basic open. -/
lemma iso_preimage_basicOpen (a : SectionGradedSum.Sections L ⊤) :
    (iso f L).hom ⁻¹ᵁ Proj.basicOpen (baseGrade f L) a =
      Proj.basicOpen (grade L ⊤) a := rfl

/-- Structural maps agree under the identity-ring Proj comparison. -/
@[reassoc]
lemma iso_toSpecBase :
    (iso f L).hom ≫ GradedProjStructuralMap.toSpecBase (baseGrade f L) =
      SectionGradedProjStructuralMap.toSpecBase f L := by
  apply GradedProjStructuralNaturality.map_toSpecBase
    (baseGrade f L) (grade L ⊤) _ f.appTop.hom
  intro r
  exact structural_algebraMap f L r

/-- Unit-coordinate charts agree under the identity-ring Proj comparison. -/
@[reassoc]
lemma chart_iso {Y : Scheme} (ψ : SectionGradedSum.Sections L ⊤ →+* Γ(Y, ⊤))
    {d : ℕ} (a : SectionGradedSum.Sections L ⊤) (ha : a ∈ grade L ⊤ d) (hd : 0 < d)
    (hu : IsUnit (ψ a)) :
    GradedProjUnitChart.toProj (grade L ⊤) ψ a hu ha hd ≫ (iso f L).hom =
      GradedProjUnitChart.toProj (baseGrade f L) ψ a hu ha hd := by
  exact GradedProjUnitChartMap.toProj_map (baseGrade f L) (grade L ⊤)
    (GradedProjRingEquiv.forward _ _ (RingEquiv.refl _) (fun _ _ ↦ Iff.rfl)) ψ
    (GradedProjRingEquiv.irrelevant_le_forward _ _ _ _) a ha hd hu

end FLT.Mazur.SectionGradedProjGrading

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonReflectionFullFamily
public import FLT.Mazur.ProjectiveLineMarkedCharts

/-!
# Original polygon markings under full-family reflection

The section at unit a on component i becomes the section at a inverse on
component -i. The square is cartesian, so its Cartier ideal is preserved
scheme-theoretically, including its original multiplicity.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry GrpObj
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching ProjectiveLineActionSpecialization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Reflection retains the original marking with reciprocal coordinate and negated label. -/
@[reassoc] theorem section_reflection (a : Kˣ) (i : Fin n) :
    sectionMap K n p a i ≫ (polygonReflection K hn p q h).left =
      sectionMap K n p a⁻¹ (reflectIndex i) := by
  have he := congrArg Over.Hom.left (componentι_polygonReflection K hn p q h i)
  change unitPoint K a ≫ (torusToComponent K).left ≫
    (componentι K n i).left ≫ p.left ≫ (polygonReflection K hn p q h).left = _
  rw [show (componentι K n i).left ≫ p.left ≫
      (polygonReflection K hn p q h).left = _ from he]
  have ht : (torusToComponent K).left ≫
      (ProjectiveLine.endpointReversalOverIso K).hom.left =
        (ProjectiveLine.inversion K).hom ≫ (torusToComponent K).left := by
    change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
      ProjectiveLine.endpointReversal K = _
    rw [Category.assoc, ProjectiveLine.left_endpointReversal]
    exact ProjectiveLine.endpointReversal_overlap K
  change unitPoint K a ≫ (torusToComponent K).left ≫
    (ProjectiveLine.endpointReversalOverIso K).hom.left ≫
      (componentι K n (reflectIndex i) ≫ p).left = _
  rw [← Category.assoc (torusToComponent K).left, ht]
  simp only [← Category.assoc, ProjectiveLineMarkedCharts.unitPoint_inversion]
  rfl

/-- The reflection square of actual sections is cartesian on the entire singular curve. -/
theorem section_reflection_square (a : Kˣ) (i : Fin n) :
    IsPullback (𝟙 (Spec (.of K))) (sectionMap K n p a i)
      (sectionMap K n p a⁻¹ (reflectIndex i)) (polygonReflection K hn p q h).left := by
  let _ : IsIso (polygonReflection K hn p q h).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (polygonReflectionIso K hn p q h).hom))
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, section_reflection]⟩

/-- Pullback of the reflected Cartier section is exactly the original ideal sheaf. -/
theorem section_reflection_ideal (a : Kˣ) (i : Fin n) :
    (sectionMap K n p a⁻¹ (reflectIndex i)).ker.comap
        (polygonReflection K hn p q h).left = (sectionMap K n p a i).ker := by
  let _ := PolygonSeparated.cocone K n hn p q h
  let _ := FCurve.isClosedImmersion_section C.hom _
    (section_base K n p a⁻¹ (reflectIndex i))
  have H := (section_reflection_square K n hn p q h a i).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

end FLT.Mazur.PolygonMarkedSections

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationHZero
public import FLT.Mazur.PolygonIncidence
/-!
# The actual H0 branch map is cyclic incidence

The component and node H0 equivalences retain their section restrictions.
Evaluate each selected branch on componentwise constants, then subtract in
the specified zero-minus-adjacent-infinity orientation.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.StructureDirectImage
open FCurve
variable {X Y Z : Scheme.{u}}
/-- The direct-image restriction acts by the actual global-section pullback. -/
theorem restriction_appTop (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z)
    (w : s ≫ p = q) (r : Γ(Y, ⊤)) :
    (restriction s p q w).app ⊤ r = s.appTop r := by
  subst q
  rfl
end FLT.Mazur.StructureDirectImage
namespace FLT.Mazur.PolygonCohomologyIncidence
open FCurve PolygonPinching PolygonStructureInclusion PolygonBranchDifferenceSheaf
open PolygonNormalizationHZero StructureDirectImage
variable (K : Type u) [Field K] (n : ℕ) (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- A section over the base evaluates a constant to that same scalar. -/
theorem section_scalar (s : point K ⟶ component K) (a : K) :
    s.left.appTop (structureScalarMap (ProjectiveLine.toBase K) a) =
      (Scheme.ΓSpecIso (.of K)).inv a := by
  have hs : s.left ≫ ProjectiveLine.toBase K = 𝟙 _ := s.w
  change (ProjectiveLine.toBase K).appTop ≫ s.left.appTop |> fun f ↦
    f ((Scheme.ΓSpecIso (.of K)).inv a) = (Scheme.ΓSpecIso (.of K)).inv a
  rw [← Scheme.Hom.comp_appTop, hs]
  rfl
include h in
/-- The selected branch reads its specified component coordinate. -/
theorem branch_coordinate (b : Bool)
    (x : ModuleScalarH C.hom (normalizationModule K n p) 0) (i : Fin n) :
    nodeEquiv K n q (moduleScalarHMap C.hom (branchRestriction K n hn p q h b) 0 x) i =
      normalizationEquiv K n p x (if b then next hn i else i) := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).1
  rw [node_coordinate]
  change (nodeι K n i).left.appTop
    (moduleH0Equiv (nodeModule K n q)
      (moduleHMap (branchRestriction K n hn p q h b) 0 x)) = _
  rw [moduleH0Equiv_naturality]
  change (nodeι K n i).left.appTop
    ((restriction _ _ _ _).app ⊤ (moduleH0Equiv (normalizationModule K n p) x)) = _
  rw [restriction_appTop]
  change ((branchSection K n hn b).left.appTop ≫ (nodeι K n i).left.appTop)
    (moduleH0Equiv (normalizationModule K n p) x) = _
  rw [← Scheme.Hom.comp_appTop]
  have he : (nodeι K n i).left ≫ (branchSection K n hn b).left =
      (endpoint K n hn i b).left := by
    change (nodeι K n i ≫ branchSection K n hn b).left = _
    simp [nodeι, branchSection]
  rw [he]
  cases b
  · change (ProjectiveLine.zeroSection K ≫ componentι K n i).left.appTop
      (moduleH0Equiv (normalizationModule K n p) x) = _
    rw [Over.comp_left, Scheme.Hom.comp_appTop]
    change (ProjectiveLine.zeroSection K).left.appTop
      ((componentι K n i).left.appTop (moduleH0Equiv (normalizationModule K n p) x)) = _
    rw [← normalization_coordinate, section_scalar]
    rfl
  · change (ProjectiveLine.infinitySection K ≫ componentι K n (next hn i)).left.appTop
      (moduleH0Equiv (normalizationModule K n p) x) = _
    rw [Over.comp_left, Scheme.Hom.comp_appTop]
    change (ProjectiveLine.infinitySection K).left.appTop
      ((componentι K n (next hn i)).left.appTop (moduleH0Equiv (normalizationModule K n p) x)) = _
    rw [← normalization_coordinate, section_scalar]
    rfl
include h in
/-- The H0 map of the actual sheaf difference is the cyclic incidence map. -/
theorem difference_coordinates (x : ModuleScalarH C.hom (normalizationModule K n p) 0) :
    nodeEquiv K n q (moduleScalarHMap C.hom (difference K n hn p q h) 0 x) =
      PolygonIncidence.difference K hn (normalizationEquiv K n p x) := by
  have he : moduleScalarHMap C.hom (difference K n hn p q h) 0 x =
      moduleScalarHMap C.hom (branchRestriction K n hn p q h false) 0 x -
        moduleScalarHMap C.hom (branchRestriction K n hn p q h true) 0 x := by
    apply (moduleH0Equiv (nodeModule K n q)).injective
    rw [map_sub]
    change moduleH0Equiv _ (moduleHMap _ 0 x) =
      moduleH0Equiv _ (moduleHMap _ 0 x) - moduleH0Equiv _ (moduleHMap _ 0 x)
    rw [moduleH0Equiv_naturality, moduleH0Equiv_naturality, moduleH0Equiv_naturality]
    rfl
  rw [he, map_sub]
  ext i
  change nodeEquiv K n q (moduleScalarHMap C.hom (branchRestriction K n hn p q h false) 0 x) i -
    nodeEquiv K n q (moduleScalarHMap C.hom (branchRestriction K n hn p q h true) 0 x) i = _
  rw [branch_coordinate, branch_coordinate]
  rfl
end FLT.Mazur.PolygonCohomologyIncidence

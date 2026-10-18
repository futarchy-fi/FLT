/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupTestAdicComparison
public import FLT.Mazur.AffineBoundaryTestThickenings

/-!
# Original invariant test ideals on the full scalar boundary chart

The test ideal on the full scalar product pulls back to exactly the fixed
original chart ideal. This is equality of ideals, with no radical or reduction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open AffineScalarBoundaryNilpotence Scheme.IdealSheafData
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}} [IsAffine X]
  [TopologicalSpace.NoetherianSpace X] (ρ : G →* Aut X) (Z : Set X) (hZ : IsClosed Z)

omit [Finite G] [IsAffine X] [TopologicalSpace.NoetherianSpace X] in
/-- Pullback of an invariant coordinate is its original chart function. -/
theorem quotientMap_invariant_coordinate (t : invariantCoordinates ρ) :
    (quotientMap ρ).appTop ((Scheme.ΓSpecIso (.of (invariantCoordinates ρ))).inv t) =
      t.val := by
  let _ := SchemeCoordinateAction.coordinateAction ρ
  let r := CommRingCat.ofHom (FiniteGroupQuotient.inclusion G Γ(X, ⊤))
  change ((Scheme.ΓSpecIso _).inv ≫ (X.toSpecΓ ≫ Spec.map r).appTop) t = t.val
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

variable {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates ρ) (κ : R →+* T)
  {Y : Scheme.{0}} [IsAffine Y] (a : Y ⟶ X) (b : Y ⟶ boundaryProduct s κ)
  (hab : a ≫ quotientMap ρ = b ≫ boundaryProjection s κ)
local notation "tests" => closedOrbitTests ρ Z hZ

include hab in
omit [Finite G] [IsAffine X] [TopologicalSpace.NoetherianSpace X] [IsAffine Y] in
/-- The two original test coordinates agree in every affine chart over the scalar product. -/
theorem boundary_test_coordinate_eq (t : invariantCoordinates ρ) :
    b.appTop (boundaryCoordinate s κ t) = a.appTop t.val := by
  have h := congrArg (fun f ↦ f.appTop
    ((Scheme.ΓSpecIso (.of (invariantCoordinates ρ))).inv t)) hab
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  exact h.symm.trans (congrArg a.appTop (quotientMap_invariant_coordinate ρ t))

include hab in
/-- The pulled-back full-product ideal is exactly the unchanged original chart test ideal. -/
theorem boundary_test_sheaf_eq :
    (boundaryTestSheaf s κ tests).comap b = (orbitTestChartIdeal ρ Z hZ).comap a := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [ideal_comap_top, ideal_comap_top]
  simp only [boundaryTestSheaf, orbitTestChartIdeal, ofIdealTop_ideal, homOfLE_refl,
    op_id]
  rw [(boundaryProduct s κ).presheaf.map_id, X.presheaf.map_id]
  simp only [CommRingCat.hom_id, Ideal.map_id]
  rw [boundaryTestIdeal, Ideal.map_span, Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
  congr 1
  apply Set.image_congr
  intro t _
  exact boundary_test_coordinate_eq ρ s κ a b hab t

end FLT.Mazur.SchemeFiniteGroupQuotient

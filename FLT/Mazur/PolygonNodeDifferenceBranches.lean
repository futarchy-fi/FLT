/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonNodeDifferenceOpen

/-!
# The actual punctured branches inside the full node difference open

Each original Laurent branch lifts uniquely through localization at the
scaled tangent difference. The two lifts cover the whole localized scheme.
This supplies retained charts without discarding either original branch.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonNodeDifferenceBranches
open PolygonNodeEqualizer PolygonNodeLocalization
universe u
variable {R : Type u} [CommRing R] (a : Rˣ)
local notation "d" => algebraMap R (A (R := R)) (a : R) * (y - x)

/-- The actual localization inclusion of the scaled tangent difference. -/
def inclusion : Spec (.of (Localization.Away d)) ⟶ PolygonNodeBranches.node R :=
  Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away d)))

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion a) :=
  IsOpenImmersion.of_isLocalization d

/-- The full localization image is exactly the union of the two original punctures. -/
theorem inclusion_range : Set.range (inclusion a) =
    Set.range (PolygonNodeBranches.left R) ∪ Set.range (PolygonNodeBranches.right R) := by
  rw [PolygonNodeBranches.branches_cover_difference a]
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away d) d

/-- The left original branch as a map into the entire localized node. -/
def left : Spec (.of R[T;T⁻¹]) ⟶ Spec (.of (Localization.Away d)) :=
  IsOpenImmersion.lift (inclusion a) (PolygonNodeBranches.left R) (by
    rw [inclusion_range]
    exact Set.subset_union_left)

/-- The right original branch as a map into the entire localized node. -/
def right : Spec (.of R[T;T⁻¹]) ⟶ Spec (.of (Localization.Away d)) :=
  IsOpenImmersion.lift (inclusion a) (PolygonNodeBranches.right R) (by
    rw [inclusion_range]
    exact Set.subset_union_right)

instance left_isOpenImmersion : IsOpenImmersion (left a) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

instance right_isOpenImmersion : IsOpenImmersion (right a) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- Lifting retains the complete original left branch morphism. -/
@[reassoc] theorem left_inclusion : left a ≫ inclusion a = PolygonNodeBranches.left R :=
  IsOpenImmersion.lift_fac _ _ _

/-- Lifting retains the complete original right branch morphism. -/
@[reassoc] theorem right_inclusion : right a ≫ inclusion a = PolygonNodeBranches.right R :=
  IsOpenImmersion.lift_fac _ _ _

/-- Localization has exactly the original coefficient structure map. -/
@[reassoc] theorem inclusion_structure :
    inclusion a ≫ PolygonNodeBranches.toBase R =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d))) := by
  rw [inclusion, PolygonNodeBranches.toBase, ← Spec.map_comp]
  rfl

/-- The lifted left branch preserves the original coefficient map. -/
@[reassoc] theorem left_structure :
    left a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d))) =
      (MultiplicativeGroupScheme.gm R).hom := by
  rw [← inclusion_structure, ← Category.assoc, left_inclusion,
    PolygonNodeBranches.left_toBase]

/-- The lifted right branch preserves the original coefficient map. -/
@[reassoc] theorem right_structure :
    right a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d))) =
      (MultiplicativeGroupScheme.gm R).hom := by
  rw [← inclusion_structure, ← Category.assoc, right_inclusion,
    PolygonNodeBranches.right_toBase]

/-- Both lifted branches cover the entire localization, with no residual points omitted. -/
theorem branches_cover (z : Spec (.of (Localization.Away d))) :
    z ∈ Set.range (left a) ∨ z ∈ Set.range (right a) := by
  have hz : inclusion a z ∈ Set.range (PolygonNodeBranches.left R) ∪
      Set.range (PolygonNodeBranches.right R) := by
    rw [← inclusion_range]
    exact ⟨z, rfl⟩
  rcases hz with ⟨t, ht⟩ | ⟨t, ht⟩
  · left
    refine ⟨t, (inclusion a).isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun f => f t) (left_inclusion a)).trans ht
  · right
    refine ⟨t, (inclusion a).isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun f => f t) (right_inclusion a)).trans ht

end FLT.Mazur.PolygonNodeDifferenceBranches

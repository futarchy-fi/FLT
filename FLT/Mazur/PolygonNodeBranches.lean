/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MultiplicativeGroupScheme
public import FLT.Mazur.PolygonNodeLocalization

/-!
# The punctured affine node has two open Laurent branches

The branch localizations induce disjoint open immersions whose union is the
complement of the vanishing locus of both branch coordinates. Their structure
maps are the smooth multiplicative-group structure map. No assertion of
nonsmoothness at the omitted points or of polygon existence is made here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial LaurentPolynomial

universe u

namespace FLT.Mazur.PolygonNodeBranches

open PolygonNodeEqualizer PolygonNodeLocalization

variable (R : Type u) [CommRing R]

/-- The affine node defined by pairs of functions agreeing at zero. -/
abbrev node := Spec (CommRingCat.of (A (R := R)))

/-- The first punctured branch. -/
def left : Spec (CommRingCat.of R[T;T⁻¹]) ⟶ node R :=
  Spec.map (CommRingCat.ofHom leftMap)

/-- The second punctured branch. -/
def right : Spec (CommRingCat.of R[T;T⁻¹]) ⟶ node R :=
  Spec.map (CommRingCat.ofHom rightMap)

instance left_isOpenImmersion : IsOpenImmersion (left R) := by
  let := (leftMap (R := R)).toAlgebra
  let := left_isLocalization (R := R)
  exact IsOpenImmersion.of_isLocalization (x (R := R))

instance right_isOpenImmersion : IsOpenImmersion (right R) := by
  let := (rightMap (R := R)).toAlgebra
  let := right_isLocalization (R := R)
  exact IsOpenImmersion.of_isLocalization (y (R := R))

/-- The first branch is exactly the basic open of its coordinate. -/
theorem range_left :
    Set.range (left R) =
      (PrimeSpectrum.basicOpen (x (R := R)) : Set (PrimeSpectrum (A (R := R)))) := by
  let := (leftMap (R := R)).toAlgebra
  let := left_isLocalization (R := R)
  exact PrimeSpectrum.localization_away_comap_range R[T;T⁻¹] (x (R := R))

/-- The second branch is exactly the basic open of its coordinate. -/
theorem range_right :
    Set.range (right R) =
      (PrimeSpectrum.basicOpen (y (R := R)) : Set (PrimeSpectrum (A (R := R)))) := by
  let := (rightMap (R := R)).toAlgebra
  let := right_isLocalization (R := R)
  exact PrimeSpectrum.localization_away_comap_range R[T;T⁻¹] (y (R := R))

/-- Away from the node, the branches do not meet. -/
theorem disjoint_ranges : Disjoint (Set.range (left R)) (Set.range (right R)) := by
  rw [range_left, range_right]
  change Disjoint (PrimeSpectrum.basicOpen (x (R := R)) :
    Set (PrimeSpectrum (A (R := R)))) (PrimeSpectrum.basicOpen (y (R := R)))
  rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf,
    ← PrimeSpectrum.basicOpen_mul, x_mul_y, PrimeSpectrum.basicOpen_zero]
  rfl

/-- The two Laurent charts cover the complement of the coordinate vanishing locus. -/
theorem branches_cover_complement :
    Set.range (left R) ∪ Set.range (right R) =
      (PrimeSpectrum.zeroLocus {x (R := R), y (R := R)})ᶜ := by
  rw [range_left, range_right]
  change (PrimeSpectrum.basicOpen (x (R := R)) : Set (PrimeSpectrum (A (R := R)))) ∪
    PrimeSpectrum.basicOpen (y (R := R)) = _
  ext p
  simp only [Set.mem_union, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.insert_subset_iff,
    Set.singleton_subset_iff, not_and_or]

/-- The node's structure morphism uses the diagonal inclusion of constants. -/
def toBase : node R ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (A (R := R))))

@[reassoc (attr := simp)]
theorem left_toBase : left R ≫ toBase R = (MultiplicativeGroupScheme.gm R).hom := by
  have h : (leftMap (R := R)).comp (algebraMap R (A (R := R))) =
      algebraMap R R[T;T⁻¹] := by
    apply RingHom.ext
    intro r
    exact Polynomial.toLaurent_C r
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

@[reassoc (attr := simp)]
theorem right_toBase : right R ≫ toBase R = (MultiplicativeGroupScheme.gm R).hom := by
  have h : (rightMap (R := R)).comp (algebraMap R (A (R := R))) =
      algebraMap R R[T;T⁻¹] := by
    apply RingHom.ext
    intro r
    exact Polynomial.toLaurent_C r
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

instance smooth_left : Smooth (left R ≫ toBase R) := by
  rw [left_toBase]
  exact MultiplicativeGroupScheme.smooth R

instance smooth_right : Smooth (right R ≫ toBase R) := by
  rw [right_toBase]
  exact MultiplicativeGroupScheme.smooth R

end FLT.Mazur.PolygonNodeBranches

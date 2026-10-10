/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchSwap
public import FLT.Mazur.PolygonSmoothingSpecialFiber
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The actual punctured branch opens and their intersection

Both branch inclusions are open immersions from the coefficient torus.
Their intersection in the smoothing chart is exactly the inverse image of
D(t) in the base. In particular the two opens are disjoint at parameter zero.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.PolygonSmoothing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The common coefficient torus used to parameterize either punctured branch. -/
def branchTorus : Scheme := Spec (.of R[T;T⁻¹])

/-- The first puncture's Laurent identification on actual spectra. -/
def leftPunctureIso (t : R) : branchTorus R ≅ Spec (.of (LeftPuncture t)) :=
  Scheme.Spec.mapIso (leftPunctureEquiv t).toRingEquiv.toCommRingCatIso.op

/-- The second puncture's Laurent identification on actual spectra. -/
def rightPunctureIso (t : R) : branchTorus R ≅ Spec (.of (RightPuncture t)) :=
  Scheme.Spec.mapIso (rightPunctureEquiv t).toRingEquiv.toCommRingCatIso.op

/-- The first actual punctured branch inclusion. -/
def leftBranchOpen (t : R) : branchTorus R ⟶ chart R t :=
  (leftPunctureIso R t).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (ChartRing t) (LeftPuncture t)))

/-- The second actual punctured branch inclusion. -/
def rightBranchOpen (t : R) : branchTorus R ⟶ chart R t :=
  (rightPunctureIso R t).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (ChartRing t) (RightPuncture t)))

instance leftBranchOpen_isOpenImmersion (t : R) : IsOpenImmersion (leftBranchOpen R t) := by
  let _ : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (ChartRing t) (LeftPuncture t)))) :=
    IsOpenImmersion.of_isLocalization (leftCoordinate t)
  unfold leftBranchOpen
  infer_instance

instance rightBranchOpen_isOpenImmersion (t : R) : IsOpenImmersion (rightBranchOpen R t) := by
  let _ : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (ChartRing t) (RightPuncture t)))) :=
    IsOpenImmersion.of_isLocalization (rightCoordinate t)
  unfold rightBranchOpen
  infer_instance

/-- The first branch inclusion preserves the original arithmetic base. -/
@[reassoc] theorem leftBranchOpen_base (t : R) :
    leftBranchOpen R t ≫ chartStructure R t =
      Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change leftPunctureEquiv t
    (algebraMap (ChartRing t) _ (algebraMap R _ r)) = algebraMap R _ r
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]

/-- The second branch inclusion preserves the original arithmetic base. -/
@[reassoc] theorem rightBranchOpen_base (t : R) :
    rightBranchOpen R t ≫ chartStructure R t =
      Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change rightPunctureEquiv t
    (algebraMap (ChartRing t) _ (algebraMap R _ r)) = algebraMap R _ r
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]

/-- The first branch is the full original principal open D(x). -/
theorem leftBranchOpen_range (t : R) :
    Set.range (leftBranchOpen R t) =
      (PrimeSpectrum.basicOpen (leftCoordinate t) : Set (PrimeSpectrum (ChartRing t))) := by
  change Set.range ((PrimeSpectrum.comap (algebraMap (ChartRing t) (LeftPuncture t))) ∘
    (leftPunctureIso R t).hom) = _
  exact ((leftPunctureIso R t).hom.homeomorph.surjective.range_comp _).trans
    (PrimeSpectrum.localization_away_comap_range _ _)

/-- The second branch is the full original principal open D(y). -/
theorem rightBranchOpen_range (t : R) :
    Set.range (rightBranchOpen R t) =
      (PrimeSpectrum.basicOpen (rightCoordinate t) : Set (PrimeSpectrum (ChartRing t))) := by
  change Set.range ((PrimeSpectrum.comap (algebraMap (ChartRing t) (RightPuncture t))) ∘
    (rightPunctureIso R t).hom) = _
  exact ((rightPunctureIso R t).hom.homeomorph.surjective.range_comp _).trans
    (PrimeSpectrum.localization_away_comap_range _ _)

/-- Both punctured branches meet precisely where the smoothing parameter is invertible. -/
theorem branchOpen_intersection (t : R) :
    Set.range (leftBranchOpen R t) ∩ Set.range (rightBranchOpen R t) =
      (PrimeSpectrum.basicOpen (algebraMap R (ChartRing t) t) :
        Set (PrimeSpectrum (ChartRing t))) := by
  rw [leftBranchOpen_range, rightBranchOpen_range]
  ext z
  change (leftCoordinate t ∉ z.asIdeal ∧ rightCoordinate t ∉ z.asIdeal) ↔ _
  rw [← coordinate_relation]
  change _ ↔ leftCoordinate t * rightCoordinate t ∉ z.asIdeal
  rw [z.isPrime.mul_mem_iff_mem_or_mem, not_or]

/-- The two punctured branches are disjoint in the zero-parameter chart. -/
theorem branchOpen_zero_disjoint :
    Disjoint (Set.range (leftBranchOpen R 0)) (Set.range (rightBranchOpen R 0)) := by
  rw [Set.disjoint_iff_inter_eq_empty, branchOpen_intersection]
  simp only [map_zero, PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot]

end FLT.Mazur.PolygonSmoothing

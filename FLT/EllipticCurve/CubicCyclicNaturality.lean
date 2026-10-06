/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicPrimeCyclicSubgroups
public import FLT.EllipticCurve.CubicTorsionNaturality
/-! # Field extension and Galois compatibility of cyclic parameters -/

open AlgebraicGeometry CategoryTheory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]
variable {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra R L]
  [DecidableEq K] [DecidableEq L]

/-- The prime-generator comparison commutes with extension of coefficient fields. -/
theorem primeTorsionClassicalEquiv_map (f : K →ₐ[R] L)
    (x : pointSource K ⟶ nonzeroTorsionModel W p) :
    (primeTorsionClassicalEquiv W p Fact.out L (pointSourceMap f ≫ x)).val =
      Affine.Point.map (W' := W.toAffine) f
        (primeTorsionClassicalEquiv W p Fact.out K x).val := by
  change (classicalTorsionMulEquiv W L p
    ((pointSourceMap f ≫ x) ≫ nonzeroTorsionInclusion W p)).toAdd.val = _
  rw [Category.assoc, classicalTorsionMulEquiv_map]
  rfl

/-- Extending a generator maps its generated subgroup along the field embedding. -/
theorem primePointSubgroup_map (f : K →ₐ[R] L)
    (x : pointSource K ⟶ nonzeroTorsionModel W p) :
    (primePointSubgroup W p L (pointSourceMap f ≫ x)).val =
      (primePointSubgroup W p K x).val.map (Affine.Point.map (W' := W.toAffine) f) := by
  change AddSubgroup.zmultiples _ = (AddSubgroup.zmultiples _).map _
  rw [AddMonoidHom.map_zmultiples, primeTorsionClassicalEquiv_map]
  rfl

/-- The geometric subgroup classification commutes with extensions of fields. -/
theorem scalarQuotientPrimeSubgroupEquiv_map [IsAlgClosed K] [IsAlgClosed L]
    (f : K →ₐ[R] L) (x : pointSource K ⟶ scalarQuotientModel W p) :
    (scalarQuotientPrimeSubgroupEquiv W p L (pointSourceMap f ≫ x)).val =
      (scalarQuotientPrimeSubgroupEquiv W p K x).val.map
        (Affine.Point.map (W' := W.toAffine) f) := by
  obtain ⟨y, rfl⟩ := scalarQuotientFieldPoint_surjective W p K x
  rw [← Category.assoc, scalarQuotientPrimeSubgroupEquiv_generator,
    scalarQuotientPrimeSubgroupEquiv_generator, primePointSubgroup_map]


omit [DecidableEq K] [DecidableEq L] [IsNoetherianRing R] [IsDomain R] in
/-- Point-source maps compose contravariantly. -/
theorem pointSourceMap_comp {M : Type u} [Field M] [Algebra R M]
    (f : K →ₐ[R] L) (g : L →ₐ[R] M) :
    pointSourceMap g ≫ pointSourceMap f = pointSourceMap (g.comp f) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp _ _).symm

omit [DecidableEq K] in
/-- A parameter defined over a subfield gives a subgroup fixed by automorphisms over it. -/
theorem scalarQuotientSubgroup_fixed [IsAlgClosed L]
    (f : K →ₐ[R] L) (σ : L →ₐ[R] L) (hσ : σ.comp f = f)
    (x : pointSource K ⟶ scalarQuotientModel W p) :
    (scalarQuotientPrimeSubgroupEquiv W p L (pointSourceMap f ≫ x)).val.map
      (Affine.Point.map (W' := W.toAffine) σ) =
    (scalarQuotientPrimeSubgroupEquiv W p L (pointSourceMap f ≫ x)).val := by
  rw [← scalarQuotientPrimeSubgroupEquiv_map, ← Category.assoc,
    pointSourceMap_comp, hσ]


omit [DecidableEq K] in
/-- A rational parameter determines a Galois-stable geometric subgroup. -/
theorem rationalScalarQuotient_subgroup_galoisStable
    [Algebra K L] [IsScalarTower R K L] [IsAlgClosed L]
    (x : pointSource K ⟶ scalarQuotientModel W p) (σ : L ≃ₐ[K] L) :
    (scalarQuotientPrimeSubgroupEquiv W p L
      (pointSourceMap (IsScalarTower.toAlgHom R K L) ≫ x)).val.map
        (Affine.Point.map (W' := W.toAffine) (σ.restrictScalars R).toAlgHom) =
    (scalarQuotientPrimeSubgroupEquiv W p L
      (pointSourceMap (IsScalarTower.toAlgHom R K L) ≫ x)).val := by
  apply scalarQuotientSubgroup_fixed
  ext a
  exact σ.commutes a

end WeierstrassCurve.CubicCharts

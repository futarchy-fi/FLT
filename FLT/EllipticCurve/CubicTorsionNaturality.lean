/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionClassicalGroup

/-! # Naturality of the classical torsion comparison -/

open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
/-- Evaluation of the affine chart commutes with algebra homomorphisms. -/
theorem affineEvaluation_comp {K L : Type u} [CommRing K] [CommRing L]
    [Algebra R K] [Algebra R L] (f : K →ₐ[R] L)
    (x y : K) (h : (W.map (algebraMap R K)).toAffine.Equation x y)
    (h' : (W.map (algebraMap R L)).toAffine.Equation (f x) (f y)) :
    f.comp (affineEvaluation W x y h) = affineEvaluation W (f x) (f y) h' := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change f (affineEvaluation W x y h (coord W false i)) =
    affineEvaluation W (f x) (f y) h' (coord W false i)
  fin_cases i <;> simp

/-- The classical point morphism commutes with extension of its field of values. -/
theorem fieldPointMorphism_map {K L : Type u} [Field K] [Field L]
    [Algebra R K] [Algebra R L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[R] L)
    (P : (W.map (algebraMap R K)).toAffine.Point) :
    fieldPointMorphism W (Affine.Point.map (W' := W.toAffine) f P) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ fieldPointMorphism W P := by
  cases P with
  | zero =>
    change Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ infinity W =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ infinity W
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    exact CommRingCat.hom_ext f.comp_algebraMap.symm
  | some x y h =>
    simp only [Affine.Point.map_some, fieldPointMorphism]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    exact (congrArg AlgHom.toRingHom (affineEvaluation_comp W f x y h.1
      ((W.toAffine.baseChange_nonsingular f.injective ..).mpr h).1)).symm

/-- An algebra map induces the contravariant map of point sources. -/
def pointSourceMap {K L : Type u} [CommRing K] [CommRing L]
    [Algebra R K] [Algebra R L] (f : K →ₐ[R] L) :
    pointSource (R := R) L ⟶ pointSource K :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext f.comp_algebraMap)

/-- The classical group comparison is natural in the field of values. -/
theorem classicalPointEquiv_map [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
    {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra R L]
    [DecidableEq K] [DecidableEq L] (f : K →ₐ[R] L)
    (P : (W.map (algebraMap R K)).toAffine.Point) :
    classicalPointEquiv W L (Multiplicative.ofAdd (Affine.Point.map (W' := W.toAffine) f P)) =
      pointSourceMap f ≫ classicalPointEquiv W K (Multiplicative.ofAdd P) := by
  apply Over.OverMorphism.ext
  exact fieldPointMorphism_map W f P

open Opposite MonoidalCategory CartesianMonoidalCategory MonObj
/-- The Hopf point comparison carries postcomposition to precomposition of schemes. -/
theorem hopfPointMulEquivAux_postcomp
    (A : Type u) [CommRing A] [HopfAlgebra R A]
    (G : Over (Spec (.of R))) [GrpObj G]
    (e : Grp.mk G ≅ (hopfSpec (.of R)).obj (op (CommHopfAlgCat.of R A)))
    {K L : Type u} [CommRing K] [CommRing L] [Algebra R K] [Algebra R L]
    (f : K →ₐ[R] L) (p : WithConv (A →ₐ[R] K)) :
    hopfPointMulEquivAux A G e L (WithConv.toConv (f.comp p.ofConv)) =
      pointSourceMap f ≫ hopfPointMulEquivAux A G e K p := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (f.comp p.ofConv).toRingHom) ≫ e.inv.hom.hom.left =
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) ≫ e.inv.hom.hom.left)
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]
/-- Including a represented torsion point recovers its classical point morphism. -/
theorem classicalTorsionMulEquiv_point
    (K : Type u) [Field K] [Algebra R K] [DecidableEq K] (n : ℕ)
    (p : pointSource (R := R) K ⟶ torsionModel W n) :
    classicalPointEquiv W K
      (Multiplicative.ofAdd (classicalTorsionMulEquiv W K n p).toAdd.val) =
      p ≫ torsionInclusion W n := by
  exact (classicalPointEquiv W K).apply_symm_apply _

/-- The classical torsion comparison is natural in the field of values. -/
theorem classicalTorsionMulEquiv_map
    {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra R L]
    [DecidableEq K] [DecidableEq L] (f : K →ₐ[R] L) (n : ℕ)
    (p : pointSource (R := R) K ⟶ torsionModel W n) :
    (classicalTorsionMulEquiv W L n (pointSourceMap f ≫ p)).toAdd.val =
      Affine.Point.map (W' := W.toAffine) f
        (classicalTorsionMulEquiv W K n p).toAdd.val := by
  apply Multiplicative.ofAdd.injective
  apply (classicalPointEquiv W L).injective
  rw [classicalTorsionMulEquiv_point, classicalPointEquiv_map,
    classicalTorsionMulEquiv_point, Category.assoc]

/-- The coordinate-to-classical torsion comparison commutes with every field algebra map. -/
theorem torsionCoordinateClassicalMulEquiv_postcomp
    {K L : Type u} [Field K] [Field L] [Algebra R K] [Algebra R L]
    [DecidableEq K] [DecidableEq L] (f : K →ₐ[R] L) (n : ℕ) [NeZero n]
    (p : WithConv (torsionCoordinateRing W n →ₐ[R] K)) :
    (torsionCoordinateClassicalMulEquiv W L n (WithConv.toConv (f.comp p.ofConv))).toAdd.val =
      Affine.Point.map (W' := W.toAffine) f
        (torsionCoordinateClassicalMulEquiv W K n p).toAdd.val := by
  change (classicalTorsionMulEquiv W L n
    (hopfPointMulEquivAux _ _ (torsionCoordinateGroupIso W n) L
      (WithConv.toConv (f.comp p.ofConv)))).toAdd.val = _
  rw [hopfPointMulEquivAux_postcomp, classicalTorsionMulEquiv_map]
  rfl

end WeierstrassCurve.CubicCharts

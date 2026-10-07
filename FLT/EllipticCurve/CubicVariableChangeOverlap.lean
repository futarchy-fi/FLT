/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVariableChange
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Compatibility of Weierstrass coordinate changes on a refined overlap -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

/-- The intersection where the source Z and transformed Y are invertible. -/
abbrev VariableChangeOverlap := Localization.Away
  (algebraMap (Ring (C • W) true) (Overlap (C • W) true)
    (variableChangeInfinityDenominator W C))

/-- Restriction from the ordinary overlap. -/
def variableChangeOverlapRestriction :
    Overlap (C • W) true →ₐ[R] VariableChangeOverlap W C :=
  IsScalarTower.toAlgHom R (Overlap (C • W) true) (VariableChangeOverlap W C)

/-- Restriction from the neighborhood of infinity. -/
def variableChangeNeighborhoodRestriction :
    VariableChangeNeighborhood W C →ₐ[R] VariableChangeOverlap W C :=
  IsLocalization.Away.liftAlgHom (variableChangeInfinityDenominator W C)
    (f := IsScalarTower.toAlgHom R (Ring (C • W) true) (VariableChangeOverlap W C)) (by
      change IsUnit (algebraMap (Ring (C • W) true) (VariableChangeOverlap W C)
        (variableChangeInfinityDenominator W C))
      simpa only [← IsScalarTower.algebraMap_apply (Ring (C • W) true)
        (Overlap (C • W) true) (VariableChangeOverlap W C)] using
        (IsLocalization.Away.algebraMap_isUnit (S := VariableChangeOverlap W C)
          (algebraMap (Ring (C • W) true) (Overlap (C • W) true)
            (variableChangeInfinityDenominator W C))))

@[simp] theorem variableChangeNeighborhoodRestriction_algebraMap (x : Ring (C • W) true) :
    variableChangeNeighborhoodRestriction W C
      (algebraMap (Ring (C • W) true) (VariableChangeNeighborhood W C) x) =
      algebraMap (Ring (C • W) true) (VariableChangeOverlap W C) x := by
  simp [variableChangeNeighborhoodRestriction, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem variableChangeOverlapRestriction_loc (i : Fin 2) :
    variableChangeOverlapRestriction W C (loc (C • W) true i) =
      algebraMap (Ring (C • W) true) (VariableChangeOverlap W C) (coord (C • W) true i) :=
  (IsScalarTower.algebraMap_apply (Ring (C • W) true) (Overlap (C • W) true)
    (VariableChangeOverlap W C) _).symm


/-- The transformed homogeneous coordinates on the refined overlap. -/
def variableChangeOverlapPoint : Fin 3 → VariableChangeOverlap W C :=
  let a := algebraMap R (VariableChangeOverlap W C)
  let v := algebraMap (Ring (C • W) true) (VariableChangeOverlap W C)
  let x := v (coord (C • W) true 0)
  let z := v (coord (C • W) true 1)
  ![a (C.u : R) ^ 2 * x + a C.r * z,
    a (C.u : R) ^ 3 + a (C.u : R) ^ 2 * a C.s * x + a C.t * z, z]

theorem variableChange_overlap_affine_normalized (i : Fin 3) :
    chartPointCoords W false
      (((variableChangeOverlapRestriction W C).comp (changeChart (C • W) true)).comp
        (variableChangeAffineMap W C)) i =
      variableChangeOverlapPoint W C i *
        variableChangeOverlapRestriction W C (inv (C • W) true) := by
  let A := VariableChangeOverlap W C
  let a := algebraMap R A
  let v := algebraMap (Ring (C • W) true) A
  let x := v (coord (C • W) true 0)
  let z := v (coord (C • W) true 1)
  let s := variableChangeOverlapRestriction W C (inv (C • W) true)
  let t := variableChangeNeighborhoodRestriction W C
    (IsLocalization.Away.invSelf (variableChangeInfinityDenominator W C))
  have hz : z * s = 1 := by
    simpa only [map_mul, map_one, variableChangeOverlapRestriction_loc] using
      congrArg (variableChangeOverlapRestriction W C) (loc_mul_inv (C • W) true)
  let P : Fin 3 → A :=
    ![a (C.u : R) ^ 2 * x + a C.r * z,
      a (C.u : R) ^ 3 + a (C.u : R) ^ 2 * a C.s * x + a C.t * z, z]
  let c : Ring (C • W) false →ₐ[R] Overlap (C • W) true := changeChart (C • W) true
  have hc0 : c (coord (C • W) false 0) = loc (C • W) true 0 * inv (C • W) true :=
    changeChart_coord (C • W) true 0
  have hc1 : c (coord (C • W) false 1) = inv (C • W) true :=
    changeChart_coord (C • W) true 1
  let f := ((variableChangeOverlapRestriction W C).comp c).comp
    (variableChangeAffineMap W C)
  let g := (variableChangeNeighborhoodRestriction W C).comp (variableChangeInfinityMap W C)
  have hf : ∀ i, chartPointCoords W false f i = P i * s := by
    intro i
    fin_cases i
    · change f (coord W false 0) = (a (C.u : R) ^ 2 * x + a C.r * z) * s
      dsimp only [f, AlgHom.comp_apply]
      refine (congrArg (fun y => variableChangeOverlapRestriction W C
        (c y)) (variableChangeAffineMap_coord W C 0)).trans ?_
      simp only [variableChangeAffineCoords, Matrix.cons_val_zero, map_add, map_mul, map_pow,
        AlgHom.commutes, hc0, variableChangeOverlapRestriction_loc]
      change a (C.u : R) ^ 2 * (x * s) + a C.r =
        (a (C.u : R) ^ 2 * x + a C.r * z) * s
      linear_combination -a C.r * hz
    · change f (coord W false 1) =
        (a (C.u : R) ^ 3 + a (C.u : R) ^ 2 * a C.s * x + a C.t * z) * s
      dsimp only [f, AlgHom.comp_apply]
      refine (congrArg (fun y => variableChangeOverlapRestriction W C
        (c y)) (variableChangeAffineMap_coord W C 1)).trans ?_
      simp only [variableChangeAffineCoords, Matrix.cons_val_one, Matrix.cons_val_zero,
        map_add, map_mul, map_pow, AlgHom.commutes, hc0, hc1,
        variableChangeOverlapRestriction_loc]
      change a (C.u : R) ^ 3 * s + a (C.u : R) ^ 2 * a C.s * (x * s) + a C.t =
        (a (C.u : R) ^ 3 + a (C.u : R) ^ 2 * a C.s * x + a C.t * z) * s
      linear_combination -a C.t * hz
    · exact hz.symm
  exact hf i

theorem variableChange_overlap_infinity_normalized (i : Fin 3) :
    chartPointCoords W true
      ((variableChangeNeighborhoodRestriction W C).comp (variableChangeInfinityMap W C)) i =
      variableChangeOverlapPoint W C i * variableChangeNeighborhoodRestriction W C
        (IsLocalization.Away.invSelf (variableChangeInfinityDenominator W C)) := by
  let A := VariableChangeOverlap W C
  let a := algebraMap R A
  let v := algebraMap (Ring (C • W) true) A
  let x := v (coord (C • W) true 0)
  let z := v (coord (C • W) true 1)
  let s := variableChangeOverlapRestriction W C (inv (C • W) true)
  let t := variableChangeNeighborhoodRestriction W C
    (IsLocalization.Away.invSelf (variableChangeInfinityDenominator W C))
  have ht : (a (C.u : R) ^ 3 + a (C.u : R) ^ 2 * a C.s * x + a C.t * z) * t = 1 := by
    dsimp only [a, x, z, v, t, A]
    have h := congrArg (variableChangeNeighborhoodRestriction W C)
      (IsLocalization.Away.mul_invSelf (S := VariableChangeNeighborhood W C)
        (variableChangeInfinityDenominator W C))
    simpa only [map_mul, map_one, variableChangeNeighborhoodRestriction_algebraMap,
      variableChangeInfinityDenominator, map_add, map_pow, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply R (Ring (C • W) true)] using h
  let P : Fin 3 → A :=
    ![a (C.u : R) ^ 2 * x + a C.r * z,
      a (C.u : R) ^ 3 + a (C.u : R) ^ 2 * a C.s * x + a C.t * z, z]
  let c : Ring (C • W) false →ₐ[R] Overlap (C • W) true := changeChart (C • W) true
  have hc0 : c (coord (C • W) false 0) = loc (C • W) true 0 * inv (C • W) true :=
    changeChart_coord (C • W) true 0
  have hc1 : c (coord (C • W) false 1) = inv (C • W) true :=
    changeChart_coord (C • W) true 1
  let f := ((variableChangeOverlapRestriction W C).comp c).comp
    (variableChangeAffineMap W C)
  let g := (variableChangeNeighborhoodRestriction W C).comp (variableChangeInfinityMap W C)
  have hg : ∀ i, chartPointCoords W true g i = P i * t := by
    intro i
    fin_cases i
    · change g (coord W true 0) = (a (C.u : R) ^ 2 * x + a C.r * z) * t
      dsimp only [g, AlgHom.comp_apply]
      refine (congrArg (variableChangeNeighborhoodRestriction W C)
        (variableChangeInfinityMap_coord W C 0)).trans ?_
      simp only [variableChangeInfinityCoords, Matrix.cons_val_zero, map_mul, map_add, map_pow,
        AlgHom.commutes, variableChangeNeighborhoodRestriction_algebraMap]
      rfl
    · exact ht.symm
    · change g (coord W true 1) = z * t
      dsimp only [g, AlgHom.comp_apply]
      refine (congrArg (variableChangeNeighborhoodRestriction W C)
        (variableChangeInfinityMap_coord W C 1)).trans ?_
      simp only [variableChangeInfinityCoords, Matrix.cons_val_one, Matrix.cons_val_zero, map_mul,
        variableChangeNeighborhoodRestriction_algebraMap]
      rfl
  exact hg i

theorem variableChange_refined_overlap_agreement :
    Spec.map (CommRingCat.ofHom
        ((variableChangeOverlapRestriction W C).comp (changeChart (C • W) true)).toRingHom) ≫
        variableChangeAffineMorphism W C ≫ affineChart W =
      Spec.map (CommRingCat.ofHom (variableChangeNeighborhoodRestriction W C).toRingHom) ≫
        variableChangeInfinityMorphism W C ≫ infinityChart W := by
  have h := chart_point_agreement_of_scaled W false true _ _
    (variableChangeOverlapPoint W C) (variableChangeOverlapPoint W C) _ _
    (variableChange_overlap_affine_normalized W C)
    (variableChange_overlap_infinity_normalized W C) (fun _ _ => rfl)
  unfold variableChangeAffineMorphism variableChangeInfinityMorphism
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  exact h
/-- The refined overlap is the scheme-theoretic intersection of the two infinity opens. -/
theorem variableChange_refined_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (variableChangeOverlapRestriction W C).toRingHom))
      (Spec.map (CommRingCat.ofHom (variableChangeNeighborhoodRestriction W C).toRingHom))
      (overlapInclusion (C • W) true)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Ring (C • W) true) (VariableChangeNeighborhood W C)))) := by
  let : Algebra (VariableChangeNeighborhood W C) (VariableChangeOverlap W C) :=
    (variableChangeNeighborhoodRestriction W C).toRingHom.toAlgebra
  let : IsScalarTower (Ring (C • W) true) (VariableChangeNeighborhood W C)
      (VariableChangeOverlap W C) :=
    IsScalarTower.of_algebraMap_eq
      (R := Ring (C • W) true) (S := VariableChangeNeighborhood W C)
      (A := VariableChangeOverlap W C)
      (fun x ↦ (variableChangeNeighborhoodRestriction_algebraMap W C x).symm)
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (Overlap (C • W) true)
        (Submonoid.powers (variableChangeInfinityDenominator W C)))
      (VariableChangeOverlap W C) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization
        (Submonoid.powers (algebraMap (Ring (C • W) true) (Overlap (C • W) true)
          (variableChangeInfinityDenominator W C))) (VariableChangeOverlap W C))
  have : Algebra.IsPushout (Ring (C • W) true) (Overlap (C • W) true)
      (VariableChangeNeighborhood W C)
      (VariableChangeOverlap W C) :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers (variableChangeInfinityDenominator W C))
      (VariableChangeNeighborhood W C) (Overlap (C • W) true) (VariableChangeOverlap W C)
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout (Ring (C • W) true) (Overlap (C • W) true)
      (VariableChangeNeighborhood W C) (VariableChangeOverlap W C))


end WeierstrassCurve.CubicCharts

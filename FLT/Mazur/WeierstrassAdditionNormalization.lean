/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartOverlap
public import FLT.Mazur.WeierstrassReciprocalAdditionCompatibility

/-!
# Equality of ordinary and reciprocal addition after changing the output chart

An affine chart map with invertible y-coordinate extends to the chart overlap.
The integral transition map normalizes it into the Y = 1 chart. For inverse
ordinary and reciprocal slopes, this map equals the reciprocal addition map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Extend an affine chart map through the open where its y-coordinate is a unit. -/
def affineOutputLift (f : Coordinate W 2 →ₐ[R] S) (hy : IsUnit (f (coord W 2 1))) :
    Overlap W 2 1 →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (coord W 2 1) hy

/-- The extended output map restricts to the original affine map. -/
@[simp] theorem affineOutputLift_coord (f : Coordinate W 2 →ₐ[R] S)
    (hy : IsUnit (f (coord W 2 1))) (i : Fin 3) :
    affineOutputLift W f hy (overlapCoord W 2 1 i) = f (coord W 2 i) :=
  IsLocalization.Away.lift_eq (coord W 2 1) hy (coord W 2 i)

/-- Normalize an affine output by the actual integral chart transition map. -/
def normalizeAffineOutput (f : Coordinate W 2 →ₐ[R] S) (hy : IsUnit (f (coord W 2 1))) :
    Coordinate W 1 →ₐ[R] S :=
  (affineOutputLift W f hy).comp (transitionBase W 2 1)

/-- The normalized output recovers the affine coordinates after multiplication by y. -/
theorem normalizeAffineOutput_mul (f : Coordinate W 2 →ₐ[R] S)
    (hy : IsUnit (f (coord W 2 1))) (i : Fin 3) :
    normalizeAffineOutput W f hy (coord W 1 i) * f (coord W 2 1) = f (coord W 2 i) := by
  have hi := congrArg (affineOutputLift W f hy) (overlapInverse_mul W 2 1)
  rw [map_mul, map_one, affineOutputLift_coord] at hi
  change affineOutputLift W f hy (transitionBase W 2 1 (coord W 1 i)) * _ = _
  rw [transitionBase_coord, map_mul, affineOutputLift_coord]
  linear_combination f (coord W 2 i) * hi

/-- Multiplication by the affine y-coordinate characterizes the changed chart map. -/
theorem normalizeAffineOutput_eq (f : Coordinate W 2 →ₐ[R] S)
    (hy : IsUnit (f (coord W 2 1))) (g : Coordinate W 1 →ₐ[R] S)
    (h : ∀ i, g (coord W 1 i) * f (coord W 2 1) = f (coord W 2 i)) :
    normalizeAffineOutput W f hy = g := by
  apply hom_ext
  intro i
  exact hy.mul_left_inj.mp ((normalizeAffineOutput_mul W f hy i).trans (h i).symm)

/-- Inverting a slope reverses each of its denominator relations over any ring. -/
theorem reverse_slope_relation {l m d n : S} (hm : m * l = 1) (h : m * n = d) :
    l * d = n := by
  linear_combination n * hm - l * h

variable (f : AffineProduct W →ₐ[R] S) (m l : S) (hm : m * l = 1)
  (hl : m * (f (productY₁ W) - f (productY₂ W)) = f (productX₁ W) - f (productX₂ W))
  (hc : m * (f (productX₁ W) ^ 2 + f (productX₁ W) * f (productX₂ W) +
      f (productX₂ W) ^ 2 + algebraMap R S W.a₂ * (f (productX₁ W) + f (productX₂ W)) +
      algebraMap R S W.a₄ - algebraMap R S W.a₁ * f (productY₁ W)) =
    f (productY₁ W) + f (productY₂ W) +
      algebraMap R S W.a₁ * f (productX₂ W) + algebraMap R S W.a₃)

/-- The ordinary affine addition map determined by an invertible reciprocal slope. -/
def ordinaryFromReciprocal : Coordinate W 2 →ₐ[R] S :=
  additionHom W f l (reverse_slope_relation hm hl) (reverse_slope_relation hm hc)

/-- The inverse-slope affine map has the usual addition coordinates. -/
@[simp] theorem ordinaryFromReciprocal_coord (i : Fin 3) :
    ordinaryFromReciprocal W f m l hm hl hc (coord W 2 i) =
      ![(W.map (algebraMap R S)).toAffine.addX
          (f (productX₁ W)) (f (productX₂ W)) l,
        (W.map (algebraMap R S)).toAffine.addY
          (f (productX₁ W)) (f (productX₂ W)) (f (productY₁ W)) l, 1] i :=
  MvPolynomial.aeval_X _ _

/-- The reciprocal coordinates scale the actual ordinary chart map by the cube of m. -/
theorem ordinaryFromReciprocal_scaled (i : Fin 3) :
    reciprocalCoordinates W f m i = m ^ 3 * ordinaryFromReciprocal W f m l hm hl hc
      (coord W 2 i) := by
  rw [ordinaryFromReciprocal_coord]
  exact congrFun (reciprocalXYZ_eq_scaled_add (W.map (algebraMap R S))
    (f (productX₁ W)) (f (productX₂ W)) (f (productY₁ W)) l m hm) i

/-- On the reciprocal target open, the ordinary output y-coordinate is invertible. -/
theorem ordinaryFromReciprocal_y_isUnit :
    IsUnit ((reciprocalTargetRestriction W f m).comp
      (ordinaryFromReciprocal W f m l hm hl hc) (coord W 2 1)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (reciprocalCoordinates W f m 1)
    (S := ReciprocalTargetOpen W f m)
  change IsUnit (reciprocalTargetRestriction W f m (reciprocalCoordinates W f m 1)) at hu
  have hs := congrArg (reciprocalTargetRestriction W f m)
    (ordinaryFromReciprocal_scaled W f m l hm hl hc 1)
  rw [map_mul] at hs
  rw [hs] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- The actual maps agree after the ordinary output is changed to the Y = 1 chart. -/
theorem reciprocalAddition_eq_normalized_ordinary :
    normalizeAffineOutput W
      ((reciprocalTargetRestriction W f m).comp (ordinaryFromReciprocal W f m l hm hl hc))
      (ordinaryFromReciprocal_y_isUnit W f m l hm hl hc) =
      reciprocalAddition W f m hl hc := by
  apply normalizeAffineOutput_eq
  intro i
  have hc' (j) := congrArg (reciprocalTargetRestriction W f m)
    (ordinaryFromReciprocal_scaled W f m l hm hl hc j)
  simp only [map_mul, map_pow] at hc'
  have hi := reciprocalTargetInverse_mul W f m
  rw [hc' 1] at hi
  change reciprocalAddition W f m hl hc (coord W 1 i) *
    reciprocalTargetRestriction W f m
      (ordinaryFromReciprocal W f m l hm hl hc (coord W 2 1)) =
    reciprocalTargetRestriction W f m
      (ordinaryFromReciprocal W f m l hm hl hc (coord W 2 i))
  rw [reciprocalAddition_coord, hc' i]
  linear_combination
    reciprocalTargetRestriction W f m
      (ordinaryFromReciprocal W f m l hm hl hc (coord W 2 i)) * hi

end FLT.Mazur.WeierstrassIntegralChart

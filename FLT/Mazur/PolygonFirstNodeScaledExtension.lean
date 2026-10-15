/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeScaledBoundary
public import FLT.Mazur.PolygonFirstNodeExtensionObstruction

/-!
# Exact boundary obstruction with an arbitrary original scaling

The positive-part construction also gives genuine node automorphisms with
any specified scaling reduction. Normalizing any possible extension shows
that its obstruction is exactly the same nonpositive Laurent tail.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentPositivePart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable {R : Type} [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)

/-- A full original-node automorphism extending the scaled positive part. -/
def firstNodeScaledPositiveExtension (a : (S)ˣ) (q : R[T;T⁻¹]) : (B) ≃ₐ[S] (B) :=
  (reciprocalScaleEquiv (e) a).trans (firstNodePositiveExtension q)

/-- The constructed extension retains the prescribed scaling on the entire closed node. -/
theorem firstNodeScaledPositiveExtension_reduction (a : (S)ˣ) (q : R[T;T⁻¹]) (z : B) :
    firstNodeReduction R (firstNodeScaledPositiveExtension a q z) =
      firstNodeReduction R (reciprocalScale (e) a z) :=
  firstNodePositiveExtension_reduction q _

/-- Its full Laurent restriction is the scaled constructed polynomial boundary. -/
theorem firstNodeScaledPositiveExtension_leftLaurent (a : (S)ˣ) (q : R[T;T⁻¹]) :
    leftLaurentMap (e) (firstNodeScaledPositiveExtension a q (leftCoordinate (e))) =
      C a.val * firstOrderLaurentCoordinate (positivePart q).toLaurent := by
  change leftLaurentMap (e)
    (firstNodePositiveExtension q (reciprocalScale (e) a (leftCoordinate (e)))) = _
  rw [reciprocalScale_left, map_mul, AlgEquiv.commutes, map_mul, AlgHom.commutes,
    firstNodePositiveExtension_leftLaurent]
  rfl

/-- Any original scaling-reducing extension forces the same exact tail to vanish. -/
theorem firstNodeScaledExtension_boundaryTail_zero (a : (S)ˣ) (q : R[T;T⁻¹])
    (f : (B) →ₐ[S] (B))
    (hf : ∀ z, firstNodeReduction R (f z) = firstNodeReduction R (reciprocalScale (e) a z))
    (hx : leftLaurentMap (e) (f (leftCoordinate (e))) =
      C a.val * (firstOrderCoordinateUnit q).val) : boundaryTail q = 0 := by
  apply firstNodeExtension_boundaryTail_zero q (firstNodeScaleNormalize R a f)
    (firstNodeScaleNormalize_reduction R a f hf)
  have he := congrArg (leftLaurentMap (e)) (firstNodeScaleNormalize_left R a f)
  rw [map_mul, AlgHom.commutes, hx] at he
  exact (Units.map (C : (S) →+* (S)[T;T⁻¹]).toMonoidHom a).isUnit.mul_left_cancel he

/-- Vanishing of the tail is sufficient for the explicit scaled automorphism to be exact. -/
theorem firstNodeScaledPositiveExtension_exact (a : (S)ˣ) (q : R[T;T⁻¹])
    (hq : boundaryTail q = 0) :
    leftLaurentMap (e) (firstNodeScaledPositiveExtension a q (leftCoordinate (e))) =
      C a.val * (firstOrderCoordinateUnit q).val := by
  rw [firstNodeScaledPositiveExtension_leftLaurent,
    (positivePart_toLaurent_iff q).mpr hq, firstOrderCoordinateUnit_val]

/-- The criterion concerns existence of an actual original-node automorphism. -/
theorem exists_firstNodeScaledAutomorphism_iff (a : (S)ˣ) (q : R[T;T⁻¹]) :
    (∃ f : (B) ≃ₐ[S] (B),
      (∀ z, firstNodeReduction R (f z) =
        firstNodeReduction R (reciprocalScale (e) a z)) ∧
      leftLaurentMap (e) (f (leftCoordinate (e))) =
        C a.val * (firstOrderCoordinateUnit q).val) ↔ boundaryTail q = 0 := by
  constructor
  · rintro ⟨f, hf, hx⟩
    exact firstNodeScaledExtension_boundaryTail_zero a q f.toAlgHom hf hx
  · intro hq
    exact ⟨firstNodeScaledPositiveExtension a q,
      firstNodeScaledPositiveExtension_reduction a q,
      firstNodeScaledPositiveExtension_exact a q hq⟩

end FLT.Mazur.PolygonInfinitesimalStages

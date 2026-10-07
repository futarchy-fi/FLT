/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartOverlap
public import FLT.Mazur.WeierstrassProjectiveChartProduct

/-!
# Concrete overlaps of integral input-chart products

Tensoring the two principal chart overlaps gives the simultaneous input-chart
change. The two presentations are explicitly isomorphic. Every product-valued
point on which the two new coordinates are units lifts to this overlap.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j k j' k' : Fin 3)

/-- Restriction from a single chart to a principal overlap. -/
def overlapRestriction : Coordinate W j →ₐ[R] Overlap W j k :=
  IsScalarTower.toAlgHom R (Coordinate W j) (Overlap W j k)

/-- The ring of the simultaneous principal opens in the two input factors. -/
def ProductOverlap := Overlap W j j' ⊗[R] Overlap W k k'

instance : CommRing (ProductOverlap W j k j' k') :=
  inferInstanceAs (CommRing (Overlap W j j' ⊗[R] Overlap W k k'))

instance : Algebra R (ProductOverlap W j k j' k') :=
  inferInstanceAs (Algebra R (Overlap W j j' ⊗[R] Overlap W k k'))

/-- Restrict the original input product to the simultaneous overlap. -/
def productOverlapRestriction : ChartProduct W j k →ₐ[R] ProductOverlap W j k j' k' :=
  Algebra.TensorProduct.map (overlapRestriction W j j') (overlapRestriction W k k')

/-- Read the new input charts on the same overlap by normalizing each factor. -/
def productOverlapOther : ChartProduct W j' k' →ₐ[R] ProductOverlap W j k j' k' :=
  Algebra.TensorProduct.map (transitionBase W j j') (transitionBase W k k')

/-- The coordinate changes on both factors give an actual overlap isomorphism. -/
def productOverlapEquiv : ProductOverlap W j' k' j k ≃ₐ[R] ProductOverlap W j k j' k' :=
  Algebra.TensorProduct.congr (overlapEquiv W j j') (overlapEquiv W k k')

/-- The overlap isomorphism intertwines the two concrete input restrictions. -/
theorem productOverlapEquiv_restriction :
    (productOverlapEquiv W j k j' k').toAlgHom.comp
      (productOverlapRestriction W j' k' j k) = productOverlapOther W j k j' k' := by
  change (Algebra.TensorProduct.map (transition W j j') (transition W k k')).comp
    (Algebra.TensorProduct.map _ _) =
      Algebra.TensorProduct.map (transitionBase W j j') (transitionBase W k k')
  rw [← Algebra.TensorProduct.map_comp]
  congr 1
  · apply hom_ext
    intro i
    exact (transition_coord W j j' i).trans (transitionBase_coord W j j' i).symm
  · apply hom_ext
    intro i
    exact (transition_coord W k k' i).trans (transitionBase_coord W k k' i).symm

/-- Localize a chart-valued point at any coordinate whose value is a unit. -/
def overlapLift (f : Coordinate W j →ₐ[R] S) (h : IsUnit (f (coord W j k))) :
    Overlap W j k →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (coord W j k) h

/-- The lift retains the given chart-valued point. -/
@[simp] theorem overlapLift_restriction (f : Coordinate W j →ₐ[R] S)
    (h : IsUnit (f (coord W j k))) :
    (overlapLift W j k f h).comp (overlapRestriction W j k) = f := by
  apply AlgHom.ext
  intro a
  exact IsLocalization.Away.lift_eq (coord W j k) h a

/-- A point with both new coordinates invertible lifts to the product overlap. -/
def productOverlapLift (f : ChartProduct W j k →ₐ[R] S)
    (hl : IsUnit (f (chartProductLeft W j k (coord W j j'))))
    (hr : IsUnit (f (chartProductRight W j k (coord W k k')))) :
    ProductOverlap W j k j' k' →ₐ[R] S :=
  Algebra.TensorProduct.lift
    (overlapLift W j j' (f.comp (chartProductLeft W j k)) hl)
    (overlapLift W k k' (f.comp (chartProductRight W j k)) hr)
    (fun _ _ => Commute.all ..)

/-- The constructed overlap point restricts to the original product point. -/
theorem productOverlapLift_restriction (f : ChartProduct W j k →ₐ[R] S)
    (hl : IsUnit (f (chartProductLeft W j k (coord W j j'))))
    (hr : IsUnit (f (chartProductRight W j k (coord W k k')))) :
    (productOverlapLift W j k j' k' f hl hr).comp
      (productOverlapRestriction W j k j' k') = f := by
  apply chartProduct_hom_ext
  · change ((Algebra.TensorProduct.lift _ _ _).comp
        (Algebra.TensorProduct.map _ _)).comp Algebra.TensorProduct.includeLeft = _
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft,
      ← AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeLeft]
    exact overlapLift_restriction W j j' _ hl
  · change ((Algebra.TensorProduct.lift _ _ _).comp
        (Algebra.TensorProduct.map _ _)).comp Algebra.TensorProduct.includeRight = _
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight,
      ← AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeRight']
    exact overlapLift_restriction W k k' _ hr

end FLT.Mazur.WeierstrassIntegralChart

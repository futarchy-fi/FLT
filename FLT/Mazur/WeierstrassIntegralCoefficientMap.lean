/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientMap
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# Coefficient extension of the actual integral cubic

Coefficient maps commute with the integral normalization transitions. Thus the
actual chart maps descend to a scheme morphism between the glued cubics, over
the corresponding map of coefficient spectra.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Coefficient extension commutes with restriction from a normalized chart to its overlap. -/
theorem overlapCoefficientMap_restriction (j k : Fin 3) :
    (overlapCoefficientMap (S := S) W j k).comp (overlapRestriction W j k) =
      ((overlapRestriction (W.map (algebraMap R S)) j k).restrictScalars R).comp
        (chartCoefficientMap W j) := by
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord]
  exact overlapCoefficientMap_coord (S := S) W j k i

/-- Coefficient extension commutes with the actual normalization transition. -/
theorem overlapCoefficientMap_transition (j k : Fin 3) :
    (overlapCoefficientMap (S := S) W j k).comp (transition W j k) =
      ((transition (W.map (algebraMap R S)) j k).restrictScalars R).comp
        (overlapCoefficientMap W k j) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coord W k j))
  apply hom_ext
  intro i
  change overlapCoefficientMap W j k (transition W j k (overlapCoord W k j i)) =
    transition (W.map (algebraMap R S)) j k
      (overlapCoefficientMap W k j (overlapCoord W k j i))
  rw [transition_coord, map_mul, overlapCoefficientMap_inverse,
    overlapCoefficientMap_coord, overlapCoefficientMap_coord, transition_coord]

/-- The normalized chart morphism induced by coefficient extension. -/
def chartCoefficientMorphism (j : Fin 3) :
    chartScheme (W.map (algebraMap R S)) j ⟶ chartScheme W j :=
  Spec.map (CommRingCat.ofHom (chartCoefficientMap W j).toRingHom)

/-- The principal-overlap morphism induced by coefficient extension. -/
def overlapCoefficientMorphism (j k : Fin 3) :
    overlapScheme (W.map (algebraMap R S)) j k ⟶ overlapScheme W j k :=
  Spec.map (CommRingCat.ofHom (overlapCoefficientMap W j k).toRingHom)

/-- Restriction commutes with the concrete coefficient morphisms. -/
@[reassoc] theorem overlapCoefficientMorphism_inclusion (j k : Fin 3) :
    overlapCoefficientMorphism (S := S) W j k ≫ overlapInclusion W j k =
      overlapInclusion (W.map (algebraMap R S)) j k ≫ chartCoefficientMorphism W j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (overlapCoefficientMap_restriction W j k)

/-- Normalization commutes with the concrete coefficient morphisms. -/
@[reassoc] theorem overlapCoefficientMorphism_transition (j k : Fin 3) :
    overlapCoefficientMorphism (S := S) W j k ≫ chartTransition W j k =
      chartTransition (W.map (algebraMap R S)) j k ≫ overlapCoefficientMorphism W k j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (overlapCoefficientMap_transition W j k)

/-- The local coefficient morphisms agree on overlaps of the extended cubic. -/
theorem chartCoefficientMorphism_compatibility (j k : Fin 3) :
    overlapInclusion (W.map (algebraMap R S)) j k ≫
        (chartCoefficientMorphism W j ≫ integralCurveChart W j) =
      chartTransition (W.map (algebraMap R S)) j k ≫
        overlapInclusion (W.map (algebraMap R S)) k j ≫
          (chartCoefficientMorphism W k ≫ integralCurveChart W k) := by
  rw [← overlapCoefficientMorphism_inclusion_assoc,
    ← overlapCoefficientMorphism_inclusion_assoc,
    ← overlapCoefficientMorphism_transition_assoc,
    integralCurveChart_compatibility]

/-- The genuine morphism from the coefficient-extended cubic to the original cubic. -/
def integralCoefficientMorphism : integralCurve (W.map (algebraMap R S)) ⟶ integralCurve W :=
  integralCurveDesc _ (fun j => chartCoefficientMorphism W j ≫ integralCurveChart W j)
    (chartCoefficientMorphism_compatibility W)

/-- Descent retains each original coefficient map on the affine charts. -/
@[reassoc] theorem integralCurveChart_coefficientMorphism (j : Fin 3) :
    integralCurveChart (W.map (algebraMap R S)) j ≫ integralCoefficientMorphism W =
      chartCoefficientMorphism W j ≫ integralCurveChart W j :=
  integralCurveChart_desc _ _ _ j

/-- The global coefficient morphism lies over the expected coefficient-spectrum map. -/
@[reassoc] theorem integralCoefficientMorphism_structure :
    integralCoefficientMorphism (S := S) W ≫ integralCurveStructure W =
      integralCurveStructure (W.map (algebraMap R S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply integralCurve_hom_ext
  intro j
  rw [← Category.assoc, integralCurveChart_coefficientMorphism, Category.assoc,
    integralCurveChart_structure, ← Category.assoc, integralCurveChart_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (chartCoefficientMap W j).commutes

end FLT.Mazur.WeierstrassIntegralChart

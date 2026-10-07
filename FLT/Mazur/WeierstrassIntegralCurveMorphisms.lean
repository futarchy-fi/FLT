/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveGluing
public import FLT.Mazur.WeierstrassProductOverlap

/-!
# Morphisms to and from the glued integral cubic

Compatible chart morphisms descend, the coefficient maps define the structure
morphism, and an explicit overlap-valued output identifies two local laws as
maps into the same global curve.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual open cover of the integral cubic by its three charts. -/
def integralCurveOpenCover : (integralCurve W).OpenCover :=
  (integralCurveGlueData W).openCover

/-- Descend compatible maps from the three normalized charts. -/
def integralCurveDesc {X : Scheme.{u}} (f : ∀ j, chartScheme W j ⟶ X)
    (hf : ∀ j k, overlapInclusion W j k ≫ f j =
      chartTransition W j k ≫ overlapInclusion W k j ≫ f k) : integralCurve W ⟶ X :=
  Multicoequalizer.desc (integralCurveGlueData W).toGlueData.diagram X (fun j => f j.down)
    (fun p => by
      change overlapInclusion W p.1.down p.2.down ≫ f p.1.down =
        (chartTransition W p.1.down p.2.down ≫ overlapInclusion W p.2.down p.1.down) ≫
          f p.2.down
      rw [Category.assoc]
      exact hf p.1.down p.2.down)

/-- Descent recovers each original chart map. -/
theorem integralCurveChart_desc {X : Scheme.{u}} (f : ∀ j, chartScheme W j ⟶ X)
    (hf : ∀ j k, overlapInclusion W j k ≫ f j =
      chartTransition W j k ≫ overlapInclusion W k j ≫ f k) (j : Fin 3) :
    integralCurveChart W j ≫ integralCurveDesc W f hf = f j :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- Maps from the cubic are determined on the concrete affine charts. -/
theorem integralCurve_hom_ext {X : Scheme.{u}} (f g : integralCurve W ⟶ X)
    (h : ∀ j, integralCurveChart W j ≫ f = integralCurveChart W j ≫ g) : f = g :=
  (integralCurveOpenCover W).hom_ext f g (fun j => h j.down)

/-- The coefficient structure map on each affine chart. -/
def chartStructure (j : Fin 3) : chartScheme W j ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W j)))

/-- The structure maps are unchanged by chart normalization. -/
theorem chartStructure_compatibility (j k : Fin 3) :
    overlapInclusion W j k ≫ chartStructure W j =
      chartTransition W j k ≫ overlapInclusion W k j ≫ chartStructure W k := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact ((transition W j k).commutes r).symm

/-- The glued integral cubic as a scheme over the coefficient ring. -/
def integralCurveStructure : integralCurve W ⟶ Spec (.of R) :=
  integralCurveDesc W (chartStructure W) (chartStructure_compatibility W)

/-- The glued structure map restricts to the original coefficient map. -/
theorem integralCurveChart_structure (j : Fin 3) :
    integralCurveChart W j ≫ integralCurveStructure W = chartStructure W j :=
  integralCurveChart_desc W _ _ j

/-- Normalizing the output does not change its point on the glued curve. -/
theorem integralCurve_output_transition (j k : Fin 3) :
    Spec.map (CommRingCat.ofHom (transitionBase W j k).toRingHom) ≫
        integralCurveChart W k = overlapInclusion W j k ≫ integralCurveChart W j := by
  have he : Spec.map (CommRingCat.ofHom (transitionBase W j k).toRingHom) =
      chartTransition W j k ≫ overlapInclusion W k j := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (show transitionBase W j k =
      (transition W j k).comp (overlapRestriction W k j) from by
        apply hom_ext
        intro i
        exact (transitionBase_coord W j k i).trans (transition_coord W j k i).symm)
  rw [he, Category.assoc, integralCurveChart_compatibility]

/-- A common overlap-valued output proves equality of the global curve-valued laws. -/
theorem integralCurve_output_eq {X : Scheme.{u}} (j k : Fin 3)
    (a : X ⟶ chartScheme W j) (b : X ⟶ chartScheme W k)
    (c : X ⟶ overlapScheme W j k)
    (ha : c ≫ overlapInclusion W j k = a)
    (hb : c ≫ Spec.map (CommRingCat.ofHom (transitionBase W j k).toRingHom) = b) :
    a ≫ integralCurveChart W j = b ≫ integralCurveChart W k := by
  rw [← ha, ← hb, Category.assoc, Category.assoc, integralCurve_output_transition]

end FLT.Mazur.WeierstrassIntegralChart

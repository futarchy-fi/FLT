/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveDivisorAmpleSupport
public import FLT.Mazur.PolygonPureDimension
public import FLT.Mazur.PolygonProper
public import FLT.Mazur.DRFiberClassification
public import FLT.Mazur.SmoothCurveDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Finite-divisor ampleness on smooth curves and polygon fibers

The projective-power predicate is detected by nonempty support on smooth
geometrically integral curves, and by meeting every component on a polygon.
The component criterion also applies directly to the classified fiber core.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

namespace FLT.Mazur.FCurve

/-- The smooth geometrically integral fiber case: every nonempty finite divisor is ample. -/
theorem smooth_divisor_relativeAmple_iff_nonempty {K : Type} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyIntegral f] {I : X.IdealSheafData} (hI : EffectiveCartier I)
    [IsFinite (I.subschemeι ≫ f)] :
    RelativeAmple f (divisorLineBundle I hI) ↔ (I.support : Set X).Nonempty := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  exact divisor_relativeAmple_iff_nonempty f hI (smoothCurveDimension f inferInstance inferInstance)

/-- The component criterion applies to every supplied classified fiber, using its proved purity. -/
theorem classifiedFiber_divisor_relativeAmple_iff {K : Type} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hX : DRFiberClassification.ClassifiedFiberCore f)
    {I : X.IdealSheafData} (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ f)] :
    RelativeAmple f (divisorLineBundle I hI) ↔
      ∀ Z ∈ irreducibleComponents X, ((I.support : Set X) ∩ Z).Nonempty :=
  divisor_relativeAmple_iff_meets_components f hI hX.pureDimension

end FLT.Mazur.FCurve

namespace FLT.Mazur.PolygonPinching
open FCurve

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (CommRingCat.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- A finite Cartier divisor on a polygon is ample exactly when it meets every component. -/
theorem divisor_relativeAmple_iff_component_support {I : C.left.IdealSheafData}
    (hI : EffectiveCartier I) [IsFinite (I.subschemeι ≫ C.hom)] :
    RelativeAmple C.hom (divisorLineBundle I hI) ↔
      ∀ i : Fin n, ((I.support : Set C.left) ∩ Set.range (componentι K n i ≫ p).left).Nonempty := by
  have := PolygonProper.proper K n hn p q h
  rw [divisor_relativeAmple_iff_meets_components C.hom hI
    (PolygonPureDimension.pureDimension K n hn p q h),
    PolygonComponentImages.components_eq K n hn p q h]
  constructor
  · intro h i
    exact h _ ⟨i, rfl⟩
  · rintro h _ ⟨i, rfl⟩
    exact h i

end FLT.Mazur.PolygonPinching

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothAlgebraReduced
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth morphisms have geometrically reduced fibers

Affine smooth schemes over fields have reduced coordinate rings. Reducedness
is local on the source, and smoothness is preserved by every base change,
giving geometric reducedness without a dimension or properness hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An affine smooth scheme over a field is reduced. -/
theorem isReduced_of_affine_smooth_field {K : Type u} [Field K]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X := by
  let φ := Spec.preimage (X.isoSpec.inv ≫ f)
  let _ : Algebra K Γ(X, ⊤) := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) =
      X.isoSpec.inv ≫ f := Spec.map_preimage _
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [hφ]
    infer_instance
  have : Algebra.Smooth K Γ(X, ⊤) :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs)
  have : _root_.IsReduced Γ(X, ⊤) := isReduced_of_smooth_domain K Γ(X, ⊤)
  exact isReduced_of_isAffine_isReduced X

/-- Every smooth scheme over a field is reduced. -/
theorem isReduced_of_smooth_field {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X := by
  have (i : X.affineCover.I₀) : IsReduced (X.affineCover.X i) :=
    isReduced_of_affine_smooth_field (X.affineCover.f i ≫ f)
  exact IsReduced.of_openCover X X.affineCover

/-- All field-valued base changes of a smooth morphism are reduced. -/
theorem geometricallyReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  exact isReduced_of_smooth_field (pullback.snd f y)

/-- In particular, smooth relative-dimension-one families have geometrically reduced fibers. -/
theorem geometricallyReduced_of_smooth_curve {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 f] : GeometricallyReduced f := by
  have := SmoothOfRelativeDimension.smooth 1 f
  exact geometricallyReduced_of_smooth f

end FLT.Mazur.Approximation

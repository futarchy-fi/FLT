/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegralCurveCartierFinite
public import FLT.Mazur.RelativeCartierBaseChange
public import FLT.Mazur.CartierImmersionFinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Finite flat relative Cartier divisors on proper smooth integral curves

The full divisor over each residue field is finite by its Cartier equation.
The existing divisor base-change isomorphism identifies it with the actual
scheme-theoretic fiber. Properness then upgrades quasi-finiteness to finiteness.
No Noetherian hypothesis or fixed degree is imposed on the base.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

namespace FLT.Mazur.FCurve

variable {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
  [GeometricallyIntegral f] {I : X.IdealSheafData}

/-- The actual residue-field fiber of a relative Cartier divisor is finite. -/
theorem RelativeEffectiveCartier.isFinite_fiber [QuasiCompact f]
    (hI : RelativeEffectiveCartier f I) (s : S) :
    IsFinite ((I.subschemeι ≫ f).fiberToSpecResidueField s) := by
  let g := S.fromSpecResidueField s
  let _ : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f g inferInstance
  let _ : IsIntegral (pullback f g) := inferInstanceAs (IsIntegral (f.fiber s))
  have hc := (relativeCartierBaseChange f g I hI).1
  let _ := hc.isFinite_of_integral_smoothCurve (pullback.snd f g)
  change IsFinite (pullback.snd (I.subschemeι ≫ f) g)
  rw [← divisorBaseChangeIso_inv_subschemeι_snd f g I]
  infer_instance

/-- Relative Cartier divisors on quasi-compact smooth integral curves are quasi-finite. -/
theorem RelativeEffectiveCartier.locallyQuasiFinite [QuasiCompact f]
    (hI : RelativeEffectiveCartier f I) : LocallyQuasiFinite (I.subschemeι ≫ f) := by
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro s
  let _ := hI.isFinite_fiber f s
  infer_instance

/-- Properness makes every full relative Cartier divisor finite. -/
theorem RelativeEffectiveCartier.isFinite [IsProper f]
    (hI : RelativeEffectiveCartier f I) : IsFinite (I.subschemeι ≫ f) := by
  let _ := hI.locallyQuasiFinite f
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- The divisor is finite, flat, and finitely presented over an arbitrary original base. -/
theorem RelativeEffectiveCartier.finite_flat_presented [IsProper f]
    (hI : RelativeEffectiveCartier f I) :
    IsFinite (I.subschemeι ≫ f) ∧ Flat (I.subschemeι ≫ f) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ f) := by
  let _ := SmoothOfRelativeDimension.smooth 1 f
  exact ⟨hI.isFinite f, hI.2, hI.1.locallyOfFinitePresentation_comp f⟩

end FLT.Mazur.FCurve

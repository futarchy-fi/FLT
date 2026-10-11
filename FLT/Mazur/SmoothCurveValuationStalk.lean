/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCurveValuation
public import FLT.Mazur.SectionDivisors
public import FLT.Mazur.SmoothDimension
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Valuation stalks on integral smooth field curves

Standard smooth charts give étale polynomial coordinates. Their local valuation
rings identify with the actual scheme stalks, providing the input needed to
extend maps to proper schemes across the missing points of an affine chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

universe u

/-- Every actual stalk of an integral smooth field curve is a valuation ring. -/
theorem smoothCurve_stalk_valuationRing {K : Type u} [Field K] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : X) : ValuationRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hx, _, a, ha⟩ := exists_standardSmooth_affine_chart f 1 x
  let _ := a.toAlgebra
  let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, V) := ha
  obtain ⟨g, hg⟩ := exists_etale_polynomial_coordinate (R := K) (B := Γ(X, V))
  let _ := g.toAlgebra
  let _ : Algebra.Etale (Polynomial K) Γ(X, V) := hg
  let p := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let _ := isDomain_atPrime_of_etale_pid (Polynomial K) Γ(X, V) p
  let _ := valuationRing_atPrime_of_etale_pid (Polynomial K) Γ(X, V) p
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  let _ := hV.isLocalization_stalk ⟨x, hx⟩
  let e := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime p) (X.presheaf.stalk x)
  refine { cond' := fun b c ↦ ?_ }
  obtain ⟨d, hd⟩ := ValuationRing.cond (e.symm b) (e.symm c)
  refine ⟨e d, ?_⟩
  rcases hd with hd | hd
  · exact Or.inl (by simpa only [map_mul, AlgEquiv.apply_symm_apply] using congrArg e hd)
  · exact Or.inr (by simpa only [map_mul, AlgEquiv.apply_symm_apply] using congrArg e hd)

end FLT.Mazur.FCurve

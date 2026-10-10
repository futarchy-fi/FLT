/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StandardSmoothFiniteSupportCartier
public import FLT.Mazur.QuasiFiniteIdealQuotient
public import FLT.Mazur.SmoothDimension
public import FLT.Mazur.CartierIdealStalkNeighborhood

/-!
# Finite subschemes of smooth curves over fields are Cartier

Smooth affine charts supply actual étale coordinates. The quotient ideal is
Artinian by local quasi-finiteness of the closed subscheme. Its local regular
equation spreads to a principal neighborhood and transports to scheme sections.
This includes nonreduced finite subschemes and nonrational support points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.FCurve

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- A locally quasi-finite ideal subscheme of a smooth curve over a field is Cartier. -/
theorem effectiveCartier_of_smoothCurve_locallyQuasiFinite
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (I : X.IdealSheafData) [LocallyQuasiFinite (I.subschemeι ≫ f)] :
    EffectiveCartier I := by
  intro x
  obtain ⟨V, hV, hx, _, g, hg⟩ := exists_standardSmooth_affine_chart f 1 x
  let U : X.affineOpens := ⟨V, hV⟩
  let _ := g.toAlgebra
  let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, U) := hg
  let _ : IsArtinianRing (Γ(X, U) ⧸ I.ideal U) :=
    artinian_ideal_quotient_of_locallyQuasiFinite f I U
  obtain ⟨s, hs, a, ha, hIa⟩ := cartier_neighborhood_standardSmooth_artinian_support
    (K := K) (I.ideal U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have hxs : x ∈ X.basicOpen s := by
    have hm : hV.primeIdealOf ⟨x, hx⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hs
    change hV.fromSpec (hV.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen s at hm
    simpa only [hV.fromSpec_primeIdealOf ⟨x, hx⟩] using hm
  let _ := hV.isLocalization_basicOpen s
  obtain ⟨b, hb, hIb⟩ := regular_generator_localization_transport
    (B := Γ(X, X.basicOpen s)) (.powers s) (I.ideal U) a ha hIa
  refine ⟨X.affineBasicOpen s, hxs, b, hb, ?_⟩
  rw [← I.map_ideal_basicOpen U s]
  exact hIb

/-- In particular, every finite closed subscheme of a smooth field curve is Cartier. -/
theorem effectiveCartier_of_smoothCurve_finite
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ f)] : EffectiveCartier I :=
  effectiveCartier_of_smoothCurve_locallyQuasiFinite f I

end FLT.Mazur.FCurve

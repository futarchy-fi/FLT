/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearFiniteAffine
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
public import FLT.Mazur.SchemeUnchangedOpenPullback

/-!
# The full translated infinity open of a finite global modification

The original infinity chart and the translated affine boundary give unchanged
neighborhoods at every point of the shear preimage of the original Y-chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (r : R)
  (j : ℕ) (hj : j ≤ n)
local notation "dat" => fun a => shearData (data a) r
local notation "U" => rootShearCurve W r
local notation "C" => WeierstrassCurve.VariableChange.mk (1 : Rˣ) 0 r 0
local notation "i" => integralVariableChangeIso W U C rfl

/-- The full sheared global contraction is unchanged over the actual original infinity preimage. -/
theorem finiteGlobal_shearOriginalY_isIso :
    IsIso (finiteGlobalContraction hπ dat j hj ∣_
      (i).hom ⁻¹ᵁ (integralCurveChart W 1).opensRange) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro z hz
  obtain ⟨p, hp⟩ | ⟨p, hp⟩ := integralCurve_yz_cover U z
  · refine ⟨(integralCurveChart U 1).opensRange, ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (finiteInfinity_isPullback hπ dat j hj)
  · let V : (chartScheme U 2).Opens := PrimeSpectrum.basicOpen
      (coord U 2 1 + algebraMap R (Coordinate U 2) r * coord U 2 0)
    have hp' : p ∈ V := by
      change p ∈ PrimeSpectrum.basicOpen _
      rw [← integralShear_infinity_affine_preimage W r]
      change (i).hom (integralCurveChart U 2 p) ∈ (integralCurveChart W 1).opensRange
      rwa [hp]
    refine ⟨(V.ι ≫ integralCurveChart U 2).opensRange, ⟨⟨p, hp'⟩, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_chart_pullback _ _ _ _
      (finiteLocal_isPullback hπ dat j hj) V
      (finiteToAffine_shearOriginalY_isIso hπ data r j hj)

end FLT.Mazur.WeierstrassDividedDepth

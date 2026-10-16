/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactorRatioAffineInfinity
public import FLT.Mazur.WeierstrassModificationXFullInfinityFactorRatioBoundary

/-!
# The entire original infinity chart in the corrected polygon

The full infinity ratio lands in the actual cyclic edge. Its original
projective transition agrees with the glued full initial affine comparison
on the whole original D(y), at arbitrary nilpotent arithmetic order.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassIntegralChart PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) [Fact (IsNilpotent τ)] (k : ℕ)
  (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (hb3 : b3 ∈ I)
  (h2I : W.a₂ ∈ I) (h3I : W.a₃ ∈ I) (h4I : W.a₄ ∈ I) (h6I : W.a₆ ∈ I)

/-- The entire original infinity chart maps to the corrected polygon at its original edge. -/
def fullFactorRatioInfinityPolygonMap : Spec (.of (WeierstrassIntegralChart.Coordinate W 1)) ⟶
    PolygonInfinitesimal.scheme R τ (2 * k + 3) (by omega) :=
  infinityFactorRatioParameter W I hI h2I h3I h4I h6I s b3 r hrI hb3 ≫
    rightBranchOpen R τ ≫
      PolygonInfinitesimal.chart R τ (2 * k + 3) (by omega) (initialPolygonIndex k false)

variable (h₃ : W.a₃ = s * b3) (h₄ : W.a₄ = s * b4) (h₆ : W.a₆ = s ^ 2 * b6)

/-- The full infinity and initial affine maps agree through the actual original transition. -/
@[reassoc] theorem fullFactorRatioInfinityPolygonMap_initial :
    Spec.map (CommRingCat.ofHom (initialInfinityTransition W s b3 b4 b6 h₃ h₄ h₆).toRingHom) ≫
      fullFactorRatioInfinityPolygonMap W s τ k b3 r I hI hrI hb3 h2I h3I h4I h6I =
        polynomialInitialInfinityInclusion W s b3 b4 b6 ≫
          factorRatioInitialAffinePolygonMap W ha s τ hτ k b3 b4 b6 r hr I hI hrI hb3 := by
  rw [fullFactorRatioInfinityPolygonMap, ← Category.assoc,
    fullInfinityFactorRatioParameter_boundary W s b3 b4 b6 h₃ h₄ h₆
      I hI h2I h3I h4I h6I r hr hrI hb3,
    factorRatioInitialAffinePolygonMap_infinity_boundary]

end FLT.Mazur.WeierstrassDividedDepth

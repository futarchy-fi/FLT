/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapFactorRatioBoundary
public import FLT.Mazur.WeierstrassModificationXInitialMobiusInfinityBoundary

/-!
# Corrected reciprocal boundaries on the original infinity localization

Both actual original legs from D(y) now use one full parameter and its inverse.
The original infinity isomorphism and projective transition maps are retained.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "E" => polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI h3
local notation "i" => polynomialNodeOverlapInclusion W s
local notation "j" => polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3
local notation "C" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The exact full factor-ratio parameter on the actual original infinity boundary. -/
def factorRatioInfinityParameter : Spec (.of Y) ⟶ PolygonSmoothing.branchTorus R :=
  (E).inv ≫ factorRatioOverlapParameter W s b3 b4 b6 r hr I hI hrI h3

local notation "P" => factorRatioInfinityParameter W s b3 b4 b6 r hr I hI hrI h3

/-- The first full infinity restriction gives the corrected original polygon boundary. -/
@[reassoc] theorem factorRatioInfinityParameter_first :
    (E).inv ≫ i ≫ C = P ≫ PolygonSmoothing.rightBranchOpen R τ := by
  rw [polynomialFactorRatioChart_overlap_first, factorRatioInfinityParameter, Category.assoc]

/-- The actual opposite infinity restriction gives exact edge inversion at every order. -/
@[reassoc] theorem factorRatioInfinityParameter_opposite :
    (E).inv ≫ j ≫ C =
      P ≫ (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.rightBranchOpen R τ := by
  rw [polynomialFactorRatioChart_overlap_opposite, factorRatioInfinityParameter, Category.assoc]

end FLT.Mazur.WeierstrassModificationX

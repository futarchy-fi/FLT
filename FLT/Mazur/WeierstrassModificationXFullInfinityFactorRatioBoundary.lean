/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInfinityFactorRatioTransition
public import FLT.Mazur.WeierstrassModificationXNodeOverlapInfinityEvaluation
public import FLT.Mazur.WeierstrassModificationXFactorRatioInfinityBoundary

/-!
# The corrected original D(y) parameter extends to the entire infinity chart

The explicit full infinity ratio restricts through the actual original
projective transition to the pre-existing full boundary parameter. No
nilpotent correction, coefficient, or original localization is discarded.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (I : Ideal R) (hI : IsNilpotent I)
  (h2I : W.a₂ ∈ I) (h3I : W.a₃ ∈ I) (h4I : W.a₄ ∈ I) (h6I : W.a₆ ∈ I)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6) (hrI : r ∈ I.map C) (hb3 : b3 ∈ I)
local notation "B" => WeierstrassIntegralChart.Coordinate W 1
local notation "O" => PolynomialNodeOverlap W s
local notation "F" => initialInfinityTransition W s b3 b4 b6 h3 h4 h6
local notation "H" => polynomialNodeOverlapInfinityEvaluation W s b3 b4 b6 r hr I hI hrI hb3
local notation "G" => polynomialNodeOverlapEvaluation W s b3 b4 b6 r hr I hI hrI hb3
local notation "E" => polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI hb3
local notation "z" => infinityFactorRatioUnit W I hI h2I h3I h4I h6I s b3 r hrI hb3
local notation "v" => polynomialNodeOverlapRatio W s b3 b4 b6 r hr I hI hrI hb3
local notation "U" => polynomialOppositeFactor W s b3 b4 b6 r

/-- The entire infinity ratio induces exactly the original full node-overlap Laurent unit. -/
theorem fullInfinityFactorRatioUnit_overlap :
    Units.map ((H).comp F).toMonoidHom z = v := by
  apply Units.ext
  change H (F (z : B)) = (v : O)
  apply (polynomialNodeOverlap_opposite_isUnit W s b3 b4 b6 r hr I hI hrI hb3).mul_right_cancel
  rw [polynomialNodeOverlapRatio_denominator]
  have h := congrArg H (initialInfinityTransition_ratio_denominator
    W s b3 b4 b6 h3 h4 h6 I hI h2I h3I h4I h6I r hrI hb3)
  rw [map_mul, polynomialNodeOverlapInfinityEvaluation_base,
    polynomialNodeOverlapInfinityEvaluation_base] at h
  exact h

/-- The full original infinity chart extends the exact corrected D(y) parameter. -/
@[reassoc] theorem fullInfinityFactorRatioParameter_boundary :
    Spec.map (CommRingCat.ofHom (F).toRingHom) ≫
      infinityFactorRatioParameter W I hI h2I h3I h4I h6I s b3 r hrI hb3 =
        factorRatioInfinityParameter W s b3 b4 b6 r hr I hI hrI hb3 := by
  apply (cancel_epi (E).hom).mp
  rw [factorRatioInfinityParameter, Iso.hom_inv_id_assoc,
    polynomialNodeOverlapInfinityIso_hom_eq_spec, infinityFactorRatioParameter,
    factorRatioOverlapParameter, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (((H).comp F).comp (LaurentUnitPoints.evalUnit z)).toRingHom =
    (LaurentUnitPoints.evalUnit v).toRingHom
  rw [LaurentUnitPoints.evalUnit_natural,
    fullInfinityFactorRatioUnit_overlap W s b3 b4 b6 h3 h4 h6 I hI h2I h3I h4I h6I r hr hrI hb3]

end FLT.Mazur.WeierstrassModificationX

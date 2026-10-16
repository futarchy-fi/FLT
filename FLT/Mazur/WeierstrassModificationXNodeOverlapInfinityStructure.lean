/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapInfinityEvaluation
public import FLT.Mazur.WeierstrassModificationXInitialInfinityTransition

/-!
# Coefficient structures on the full original infinity transition

Both the full node-overlap isomorphism and the projective transition retain
all base scalars. These identities avoid unfolding localization constructions
when comparing the original arithmetic tensor projections.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "O" => PolynomialNodeOverlap W s

/-- The full original node-overlap isomorphism preserves all coefficient scalars. -/
@[reassoc] theorem polynomialNodeOverlapInfinityIso_structure :
    (polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI h3).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Y)) =
        Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [polynomialNodeOverlapInfinityIso_hom_eq_spec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext
    (polynomialNodeOverlapInfinityEvaluation W s b3 b4 b6 r hr I hI hrI h3).commutes

variable (h₃ : W.a₃ = s * b3) (h₄ : W.a₄ = s * b4) (h₆ : W.a₆ = s ^ 2 * b6)

/-- The entire original projective transition preserves its coefficient structure. -/
@[reassoc] theorem initialInfinityTransition_structure :
    Spec.map (CommRingCat.ofHom (initialInfinityTransition W s b3 b4 b6 h₃ h₄ h₆).toRingHom) ≫
      WeierstrassIntegralChart.chartStructure W 1 =
        Spec.map (CommRingCat.ofHom (algebraMap R Y)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (initialInfinityTransition W s b3 b4 b6 h₃ h₄ h₆).commutes

end FLT.Mazur.WeierstrassModificationX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryDomainLift
public import FLT.Mazur.WeierstrassReciprocalZeroPointComparison

/-!
# Reciprocal and ordinary specializations have the same actual output

An invertible reciprocal slope lifts to the ordinary domain over any algebra.
Both input homomorphisms and the morphism into the glued cubic are preserved.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (b : Bool)
  (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
  (hz : IsUnit (f (reciprocalChartAddition W b (coord W 1 2))))

/-- The ordinary replacement preserves the entire left input homomorphism. -/
theorem reciprocalAffineOrdinaryLift_left :
    (reciprocalAffineOrdinaryLift W b f hz).comp (ordinaryInputLeft W b) =
      f.comp (reciprocalInputLeft W b) := by
  simpa only [ordinaryInputLeft, reciprocalInputLeft, ← AlgHom.comp_assoc] using
    congrArg (fun g => g.comp (productLeft W))
      (reciprocalAffineOrdinaryLift_restriction W b f hz)

/-- The ordinary replacement preserves the entire right input homomorphism. -/
theorem reciprocalAffineOrdinaryLift_right :
    (reciprocalAffineOrdinaryLift W b f hz).comp (ordinaryInputRight W b) =
      f.comp (reciprocalInputRight W b) := by
  simpa only [ordinaryInputRight, reciprocalInputRight, ← AlgHom.comp_assoc] using
    congrArg (fun g => g.comp (productRight W))
      (reciprocalAffineOrdinaryLift_restriction W b f hz)

/-- The actual cubic-valued chart output is unchanged by replacing the domain. -/
theorem reciprocalAffineOrdinaryLift_output :
    Spec.map (CommRingCat.ofHom
        (reciprocalAffineOrdinaryLift W b f hz).toRingHom) ≫
        additionCurveChart W (ordinaryIndex b) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        additionCurveChart W (reciprocalIndex b) := by
  apply additionCurveChart_commonScheme
  rw [additionChartInclusion.eq_def, additionChartInclusion.eq_def,
    ← additionChartAlgRestriction_toRingHom, ← additionChartAlgRestriction_toRingHom,
    ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g : AffineProduct W →ₐ[R] S =>
    Spec.map (CommRingCat.ofHom g.toRingHom))
    (reciprocalAffineOrdinaryLift_restriction W b f hz)

end FLT.Mazur.WeierstrassIntegralChart

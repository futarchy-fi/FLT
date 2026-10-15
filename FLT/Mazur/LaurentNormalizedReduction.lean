/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentDomainPairUnits

/-!
# Reduction of normalized double Laurent units to domains

Coefficient change preserves both unit specializations. Consequently every
normalized unit reduces to the product unit over any domain quotient.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentNormalizedReduction
open PolygonScalingNaturality LaurentCoefficientEvaluation
variable {R S : Type*} [CommRing R] [CommRing S]
local notation "ε" A => AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := A) (1 : Aˣ))

/-- Coefficient change commutes with setting the first Laurent variable to one. -/
theorem firstUnit_natural (f : R →+* S) :
    (coeffMap (ε S)).comp (coeffMap (coeffMap f)) =
      (coeffMap f).comp (coeffMap (ε R)) := by
  rw [← coeffMap_comp, ← coeffMap_comp, evalOne_natural]

/-- Coefficient change commutes with setting the second Laurent variable to one. -/
theorem secondUnit_natural (f : R →+* S) :
    (ε S[T;T⁻¹]).comp (coeffMap (coeffMap f)) =
      (coeffMap f).comp (ε R[T;T⁻¹]) := evalOne_natural (coeffMap f)

/-- The universal Laurent unit is preserved by coefficient change. -/
theorem coeffMap_unit (f : R →+* S) :
    Units.map (coeffMap f).toMonoidHom (PolygonUniversalScaling.u (R := R)) =
      PolygonUniversalScaling.u := by
  apply Units.ext
  change coeffMap f (LaurentPolynomial.C 1 * LaurentPolynomial.T 1) =
    LaurentPolynomial.C 1 * LaurentPolynomial.T 1
  simp

/-- A normalized double Laurent unit has exactly the product reduction in every domain. -/
theorem reduced_eq_product [IsDomain S] (f : R →+* S) (v : R[T;T⁻¹][T;T⁻¹]ˣ)
    (h₁ : Units.map (coeffMap (ε R)).toMonoidHom v = PolygonUniversalScaling.u)
    (h₂ : Units.map (ε R[T;T⁻¹]).toMonoidHom v = PolygonUniversalScaling.u) :
    Units.map (coeffMap (coeffMap f)).toMonoidHom v =
      Units.map (LaurentPolynomial.C : S[T;T⁻¹] →+* S[T;T⁻¹][T;T⁻¹])
        (PolygonUniversalScaling.u (R := S)) * PolygonUniversalScaling.u := by
  apply LaurentDomainPairUnits.eq_product
  · apply Units.ext
    change coeffMap (ε S) (coeffMap (coeffMap f) (v : R[T;T⁻¹][T;T⁻¹])) = _
    rw [← RingHom.comp_apply, firstUnit_natural, RingHom.comp_apply]
    have he := congrArg Units.val h₁
    change coeffMap (ε R) (v : R[T;T⁻¹][T;T⁻¹]) = _ at he
    rw [he]
    exact congrArg Units.val (coeffMap_unit f)
  · apply Units.ext
    change (ε S[T;T⁻¹]) (coeffMap (coeffMap f) (v : R[T;T⁻¹][T;T⁻¹])) = _
    rw [← RingHom.comp_apply, secondUnit_natural, RingHom.comp_apply]
    have he := congrArg Units.val h₂
    change (ε R[T;T⁻¹]) (v : R[T;T⁻¹][T;T⁻¹]) = _ at he
    rw [he]
    exact congrArg Units.val (coeffMap_unit f)

end FLT.Mazur.LaurentNormalizedReduction

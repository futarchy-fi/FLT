/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentDomainUnits
public import FLT.Mazur.LaurentPairUnitSections
public import FLT.Mazur.LaurentCoefficientEvaluation

/-!
# A normalized double Laurent unit over a domain

Over a domain, the two unit slices determine a double Laurent unit. This
argument deliberately requires a domain; it does not discard nilpotent terms.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentDomainPairUnits
variable {R : Type*} [CommRing R] [IsDomain R]
local notation "ε₁" => PolygonScalingNaturality.coeffMap
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)))
local notation "ε₂" => AlgHom.toRingHom
  (LaurentUnitPoints.evalUnit (R := R[T;T⁻¹]) (1 : R[T;T⁻¹]ˣ))

/-- The two normalized slices force the product unit over a domain. -/
theorem eq_product (v : R[T;T⁻¹][T;T⁻¹]ˣ)
    (h₁ : Units.map (ε₁).toMonoidHom v = PolygonUniversalScaling.u)
    (h₂ : Units.map (ε₂).toMonoidHom v = PolygonUniversalScaling.u) :
    v = Units.map (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹])
      (PolygonUniversalScaling.u (R := R)) * PolygonUniversalScaling.u := by
  obtain ⟨a, d, hv⟩ := LaurentDomainUnits.exists_monomial v
  have ha : (a : R[T;T⁻¹]) = LaurentPolynomial.T 1 := by
    have he := congrArg Units.val h₂
    change (ε₂) (v : R[T;T⁻¹][T;T⁻¹]) = _ at he
    simpa [hv, LaurentUnitPoints.evalUnit, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit] using he
  have hd : (LaurentPolynomial.T d : R[T;T⁻¹]) = LaurentPolynomial.T 1 := by
    have he := congrArg Units.val h₁
    change (ε₁) (v : R[T;T⁻¹][T;T⁻¹]) = _ at he
    simpa [hv, ha, LaurentCoefficientEvaluation.coeffMap_T,
      PolygonScalingNaturality.coeffMap_C, LaurentUnitPoints.evalUnit,
      PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit] using he
  have hd' : d = 1 := by
    have he := congrArg LaurentPolynomial.degree hd
    simpa only [LaurentPolynomial.degree_T, WithBot.coe_inj] using he
  apply Units.ext
  simp [hv, ha, hd', PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]

end FLT.Mazur.LaurentDomainPairUnits

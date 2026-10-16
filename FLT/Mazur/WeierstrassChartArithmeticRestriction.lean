/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientRingMap
public import FLT.Mazur.WeierstrassIntegralCoefficientMap
public import FLT.Mazur.PolygonArithmeticStageRestriction
public import FLT.Mazur.WeierstrassModificationXArithmeticRestrictionMaps

/-!
# The full normalized cubic chart at consecutive arithmetic orders

The original coefficient quotient map preserves all three normalized coordinates
and both the arithmetic and integral projections of the infinity chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Ring homomorphisms of a normalized chart are determined by scalars and coordinates. -/
theorem chartRingHom_ext (W : WeierstrassCurve R) (j : Fin 3)
    (f g : Coordinate W j →+* S)
    (hc : ∀ a, f (algebraMap R _ a) = g (algebraMap R _ a))
    (hx : ∀ i, f (coord W j i) = g (coord W j i)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact hc
  · exact hx

variable (R) (π : R) (m : ℕ) (W : WeierstrassCurve R) (j : Fin 3)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁

/-- The complete chart coefficient quotient with its independently specialized target curve. -/
def arithmeticChartCoefficientRingMap : Coordinate (W.map q₁) j →+*
    Coordinate (W.map q₀) j :=
  chartCoefficientRingMapTo (restriction R π m).toRingHom (W.map q₁) j (W.map q₀)
    (arithmeticInitialCurve_restriction R π m W)

/-- Every original normalized coordinate survives the actual quotient restriction. -/
theorem arithmeticChartCoefficientRingMap_coord (i : Fin 3) :
    arithmeticChartCoefficientRingMap R π m W j (coord (W.map q₁) j i) =
      coord (W.map q₀) j i :=
  chartCoefficientRingMapTo_coord ..

/-- The full original scalar map is the actual consecutive arithmetic quotient. -/
theorem arithmeticChartCoefficientRingMap_scalar (a : Q₁) :
    arithmeticChartCoefficientRingMap R π m W j (algebraMap Q₁ _ a) =
      algebraMap Q₀ _ (restriction R π m a) :=
  chartCoefficientRingMapTo_scalar ..

/-- The actual restriction on the full normalized original cubic scheme. -/
def arithmeticChartRestriction : chartScheme (W.map q₀) j ⟶ chartScheme (W.map q₁) j :=
  Spec.map (CommRingCat.ofHom (arithmeticChartCoefficientRingMap R π m W j))

/-- Consecutive cubic restrictions preserve the whole original integral projection. -/
@[reassoc] theorem arithmeticChartRestriction_projection :
    arithmeticChartRestriction R π m W j ≫ chartCoefficientMorphism (S := Q₁) W j =
      chartCoefficientMorphism (S := Q₀) W j := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply chartRingHom_ext W j
  · intro a
    change arithmeticChartCoefficientRingMap R π m W j
      (chartCoefficientMap (S := Q₁) W j (algebraMap R _ a)) =
        chartCoefficientMap (S := Q₀) W j (algebraMap R _ a)
    rw [AlgHom.commutes, AlgHom.commutes]
    change arithmeticChartCoefficientRingMap R π m W j (algebraMap Q₁ _ (q₁ a)) =
      algebraMap Q₀ _ (q₀ a)
    rw [arithmeticChartCoefficientRingMap_scalar, (restriction R π m).commutes]
  · intro i
    change arithmeticChartCoefficientRingMap R π m W j
      (chartCoefficientMap (S := Q₁) W j (coord W j i)) =
        chartCoefficientMap (S := Q₀) W j (coord W j i)
    rw [chartCoefficientMap_coord, chartCoefficientMap_coord,
      arithmeticChartCoefficientRingMap_coord]

/-- The entire original cubic restriction retains its arithmetic coefficient projection. -/
@[reassoc] theorem arithmeticChartRestriction_structure :
    arithmeticChartRestriction R π m W j ≫ chartStructure (W.map q₁) j =
      chartStructure (W.map q₀) j ≫ baseRestriction R π m := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (arithmeticChartCoefficientRingMap_scalar R π m W j))

end FLT.Mazur.WeierstrassIntegralChart

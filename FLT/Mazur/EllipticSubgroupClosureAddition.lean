/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureProductDensity

/-!
# Ambient addition descends to the actual subgroup closure

In good reduction, addition sends every integral subgroup pair to its subgroup
sum. Proved schematic density of those pairs forces preservation of the closure
ideal and constructs multiplication on the entire closure product.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The original sums of integral subgroup sections, collected into one morphism. -/
def closureSectionSumsMap : (∐ fun _ : H × H => Spec (.of A)) ⟶ gluedClosure A W H 1 2 :=
  Sigma.desc (fun PQ => integralSection A W H (PQ.1 + PQ.2))

omit [Finite H] in
/-- Ambient addition on the actual dense family retains the original subgroup sums. -/
theorem closureSectionSumsMap_toCurve (hΔ : IsUnit W.Δ) :
    closureSectionPairsMap A W H ≫ closureProductToCurve A W H ≫
      integralCurveAddition W hΔ = closureSectionSumsMap A W H ≫ closureToCurve A W H 1 2 := by
  apply Sigma.hom_ext
  rintro ⟨P, Q⟩
  rw [closureSectionPairsMap_point_assoc, closureSectionPair_toCurve_assoc,
    ambientSectionPair_addition, closureSectionSumsMap, Sigma.ι_comp_desc_assoc]

variable [IsDedekindDomain A]

/-- Every closure equation vanishes after ambient addition on the entire closure product. -/
theorem closureAddition_preserves_ideal (hΔ : IsUnit W.Δ) :
    (closureToCurve A W H 1 2).ker ≤
      (closureProductToCurve A W H ≫ integralCurveAddition W hΔ).ker := by
  rw [← closureSectionPairsMap_ker_comp A W H, closureSectionSumsMap_toCurve]
  exact Scheme.Hom.le_ker_comp _ _

/-- The actual ambient multiplication restricted to the whole subgroup closure product. -/
def closureAddition (hΔ : IsUnit W.Δ) : closureProduct A W H ⟶ gluedClosure A W H 1 2 :=
  closureToCurveLift A W H (closureProductToCurve A W H ≫ integralCurveAddition W hΔ)
    (closureAddition_preserves_ideal A W H hΔ)

/-- The constructed multiplication is the restriction of the original ambient addition. -/
@[reassoc] theorem closureAddition_toCurve (hΔ : IsUnit W.Δ) :
    closureAddition A W H hΔ ≫ closureToCurve A W H 1 2 =
      closureProductToCurve A W H ≫ integralCurveAddition W hΔ :=
  closureToCurveLift_inclusion A W H _ _

/-- Closure multiplication is a morphism over the valuation ring. -/
@[reassoc] theorem closureAddition_toBase (hΔ : IsUnit W.Δ) :
    closureAddition A W H hΔ ≫ closureToBase A W H 1 2 =
      pullback.fst _ _ ≫ closureToBase A W H 1 2 := by
  calc
    _ = closureAddition A W H hΔ ≫ closureToCurve A W H 1 2 ≫
        integralCurveStructure W := by rw [closureToCurve_structure]
    _ = _ := by rw [closureAddition_toCurve_assoc, integralCurveAddition_structure,
      closureProductToCurve_fst_assoc, closureToCurve_structure]

/-- The constructed operation sends each integral pair to its original subgroup sum. -/
@[reassoc] theorem closureSectionPair_addition (hΔ : IsUnit W.Δ) (P Q : H) :
    closureSectionPair A W H P Q ≫ closureAddition A W H hΔ =
      integralSection A W H (P + Q) := by
  apply closureToCurve_hom_ext A W H
  rw [Category.assoc, closureAddition_toCurve, closureSectionPair_toCurve_assoc,
    ambientSectionPair_addition]

/-- The descended multiplication as a morphism in the category over the valuation ring. -/
def closureOverAddition (hΔ : IsUnit W.Δ) :
    Over.mk (closureToBase A W H 1 2) ⊗ Over.mk (closureToBase A W H 1 2) ⟶
      Over.mk (closureToBase A W H 1 2) :=
  Over.homMk (closureAddition A W H hΔ) (closureAddition_toBase A W H hΔ)

end FLT.Mazur.EllipticSubgroupChart

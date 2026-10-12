/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertGrassmannianFamilyCompatibility
public import FLT.Mazur.HilbertChartIdentityIdeal

/-!
# The global Grassmannian morphism on the original universal Hilbert chart

Restricting the global morphism to a prescribed-basis chart classifies its
entire original universal ideal. Its residue rank is proved from the actual
quotient basis after scalar extension.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ) (w : Fin d → MvPolynomial I R)
local notation "C" => ChartRing R I d w
local notation "J" => chartIdentityIdeal R I d w

/-- Cache the original coefficient quotient. -/
local instance identityGrassmannianCoefficientsRing : CommRing (Coefficients R I d) :=
  inferInstance
/-- Cache the original chart ring. -/
local instance identityGrassmannianChartRing : CommRing C := inferInstance
/-- Cache the full universal polynomial quotient. -/
local instance identityGrassmannianQuotientRing : CommRing (MvPolynomial I C ⧸ J) :=
  inferInstance

/-- Every residue fiber of the original universal ideal has the prescribed rank. -/
theorem chartIdentityIdeal_residueRank (p : PrimeSpectrum C) :
    Module.finrank p.asIdeal.ResidueField (MvPolynomial I p.asIdeal.ResidueField ⧸
      (J).map (MvPolynomial.map (algebraMap C p.asIdeal.ResidueField))) = d := by
  let b := ((chartIdentityBasis R I d w).baseChange p.asIdeal.ResidueField).map
    (polynomialQuotientBaseChangeEquiv I C p.asIdeal.ResidueField J).toLinearEquiv
  exact (Module.finrank_eq_card_basis b).trans (Fintype.card_fin d)

/-- The chart inclusion pulls back precisely the original identity ideal. -/
theorem polynomialParameterIdeal_chartIdentity :
    polynomialParameterIdeal R I d C (polynomialHilbertChartι R I d w)
      (polynomialHilbertChartι_over R I d w) = J := by
  have hid : Spec.map (CommRingCat.ofHom (AlgHom.id R C).toRingHom) =
      𝟙 (Spec (.of C)) := by
    change Spec.map (𝟙 (.of C)) = _
    exact Spec.map_id _
  have h := polynomialParameterIdeal_chart R I d C w (AlgHom.id R C)
    (by rw [hid, Category.id_comp]; exact polynomialHilbertChartι_over R I d w)
  change polynomialParameterIdeal R I d C (polynomialHilbertChartι R I d w) _ =
    pointIdeal R I d w (AlgHom.id R C)
  simpa only [hid, Category.id_comp] using h

variable {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)

/-- The global map on a chart classifies its original universal ideal, with every relation. -/
theorem hilbertGrassmannianMap_chartIdentity :
    polynomialHilbertChartι R I d w ≫ hilbertGrassmannianMap R I d b hκ =
      finiteFlatHilbertClassifyingMap R C I J d (chartIdentityIdeal_residueRank R I d w)
        b hκ := by
  rw [hilbertGrassmannianMap_affineTest R I d b hκ C _
    (polynomialHilbertChartι_over R I d w)]
  exact finiteFlatHilbertClassifyingMap_congr R I d b hκ C _ J _
    (chartIdentityIdeal_residueRank R I d w) (polynomialParameterIdeal_chartIdentity R I d w)

end FLT.Mazur.HilbertChart

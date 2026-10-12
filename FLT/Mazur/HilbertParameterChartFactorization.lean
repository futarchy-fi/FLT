/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialParameterInverse

/-!
# Affine parameters factor through their actual prescribed-basis charts

The full pulled-back ideal has the prescribed basis exactly when the original
parameter factors through that chart. The construction uses the chart's ideal
classification and the global inverse law for the entire universal ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (S : Type u) [CommRing S] [Algebra R S]
  (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
  (hf : f ≫ polynomialHilbertStructure R I d = Spec.algebraMap R S)
  (w : Fin d → MvPolynomial I R)
local notation "J" => polynomialParameterIdeal R I d S f hf

/-- Cache the coefficient ring of the original chart. -/
local instance factorizationCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the original chart ring. -/
local instance factorizationChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- A prescribed basis of the full pulled-back ideal constructs an actual chart lift. -/
theorem polynomialParameter_chartLift
    (hb : ∃ v : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J),
      ∀ j, polynomialBasisTuple R I d w S J j = v j) :
    ∃ g : Spec (.of S) ⟶ Spec (.of (ChartRing R I d w)),
      g ≫ polynomialHilbertChartι R I d w = f := by
  let Q : PrescribedBasisIdeals R I d w S := ⟨J, hb⟩
  let a := idealClassifyingMap R I d w S Q
  let g := Spec.map (CommRingCat.ofHom a.toRingHom)
  have hg : (g ≫ polynomialHilbertChartι R I d w) ≫
      polynomialHilbertStructure R I d = Spec.algebraMap R S := by
    rw [Category.assoc, polynomialHilbertChartι_over, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext a.comp_algebraMap)
  refine ⟨g, polynomialParameterIdeal_injective R I d S _ hg f hf ?_⟩
  rw [polynomialParameterIdeal_chart R I d S w a hg]
  exact congrArg Subtype.val (idealOfPoint_idealClassifyingMap R I d w S Q)

/-- An actual chart lift recovers the prescribed basis of the entire pulled-back ideal. -/
theorem polynomialParameter_basis_of_chartLift
    (g : Spec (.of S) ⟶ Spec (.of (ChartRing R I d w)))
    (hg : g ≫ polynomialHilbertChartι R I d w = f) :
    ∃ v : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J),
      ∀ j, polynomialBasisTuple R I d w S J j = v j := by
  have hs : g ≫ Spec.algebraMap R (ChartRing R I d w) = Spec.algebraMap R S := by
    change g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))) = _
    rw [← polynomialHilbertChartι_over R I d w, ← Category.assoc, hg, hf]
  let a := affineOverAlgHom R (ChartRing R I d w) S g hs
  have ha := affineOverAlgHom_spec R (ChartRing R I d w) S g hs
  have he : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      polynomialHilbertChartι R I d w = f := by rw [ha, hg]
  have ho : (Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      polynomialHilbertChartι R I d w) ≫ polynomialHilbertStructure R I d =
        Spec.algebraMap R S := by rw [he, hf]
  have hj : J = pointIdeal R I d w a := by
    simpa only [he] using polynomialParameterIdeal_chart R I d S w a ho
  rw [hj]
  exact (idealOfPoint R I d w a).property

/-- The unique affine lift is equivalent to the actual prescribed polynomial quotient basis. -/
theorem polynomialParameter_unique_chart_iff :
    (∃! g : Spec (.of S) ⟶ Spec (.of (ChartRing R I d w)),
      g ≫ polynomialHilbertChartι R I d w = f) ↔
    ∃ v : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J),
      ∀ j, polynomialBasisTuple R I d w S J j = v j := by
  constructor
  · rintro ⟨g, hg, _⟩
    exact polynomialParameter_basis_of_chartLift R I d S f hf w g hg
  · intro hb
    obtain ⟨g, hg⟩ := polynomialParameter_chartLift R I d S f hf w hb
    exact ⟨g, hg, fun k hk ↦ (cancel_mono (polynomialHilbertChartι R I d w)).mp
      (hk.trans hg.symm)⟩

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientAffineFactorization
public import FLT.Mazur.HilbertMonomialChartBasisCriterion
public import FLT.Mazur.HilbertParameterChartFactorization
public import FLT.Mazur.HilbertComplementSchemeCompatibility

/-!
# Reverse factorization for matching Hilbert and Grassmannian charts

On every affine test, the full Grassmannian chart inverse image is precisely
the original Hilbert chart. Both legs of the square are recovered, with their
original coefficient ring and complete universal polynomial ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)
  {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R (MvPolynomial.restrictTotalDegree I R (d + 1)))
  (hκ : Fintype.card κ = Fintype.card ι - d)
  (hm : Function.Injective m) (e : HilbertComplementMonomials I d m ≃ κ)
local notation "w" => (fun a ↦ MvPolynomial.monomial (Subtype.val (m a)) (1 : R))
local notation "c" => hilbertReindexedAmbient R I d m hm e
local notation "C" => ChartRing R I d w
local notation "j" => ambientGrassmannianChart R
  (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d c
variable (S : Type u) [CommRing S] [Algebra R S]
  (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
  (hf : f ≫ polynomialHilbertStructure R I d = Spec.algebraMap R S)

include hf in
/-- The actual affine inverse image of a matching Grassmannian chart is the Hilbert chart. -/
theorem hilbertComplement_affineFactorization_iff :
    (∃! g : Spec (.of S) ⟶ splitChartScheme R κ d,
      g ≫ j = f ≫ hilbertGrassmannianMap R I d b hκ) ↔
    ∃! k : Spec (.of S) ⟶ Spec (.of C), k ≫ polynomialHilbertChartι R I d w = f := by
  rw [hilbertGrassmannianMap_affineTest R I d b hκ S f hf]
  change (∃! g, g ≫ j = ambientClassifyingMap b
    (finiteFlatHilbertAmbientPoint R S I (polynomialParameterIdeal R I d S f hf) d
      (polynomialParameterIdeal_residueRank R I d S f hf)) hκ) ↔ _
  rw [ambientClassifyingMap_unique_chart_iff,
    hilbertMonomialChart_basis_iff, polynomialParameter_unique_chart_iff R I d S f hf w]
  simp only [polynomialBasisTuple, MvPolynomial.map_monomial, map_one]
  exact exists_congr (fun v ↦ forall_congr' (fun a ↦ eq_comm))

include hf in
/-- Every compatible affine test has one lift recovering both original chart projections. -/
theorem hilbertComplement_affineLift
    (g : Spec (.of S) ⟶ splitChartScheme R κ d)
    (h : f ≫ hilbertGrassmannianMap R I d b hκ = g ≫ j) :
    ∃! k : Spec (.of S) ⟶ Spec (.of C),
      k ≫ polynomialHilbertChartι R I d w = f ∧
        k ≫ hilbertReindexedChartMap R I d m e = g := by
  have hg : ∃! g' : Spec (.of S) ⟶ splitChartScheme R κ d,
      g' ≫ j = f ≫ hilbertGrassmannianMap R I d b hκ :=
    ⟨g, h.symm, fun g' hg' ↦ (cancel_mono j).mp (hg'.trans h)⟩
  obtain ⟨k, hk, hu⟩ :=
    (hilbertComplement_affineFactorization_iff R I d m b hκ hm e S f hf).mp hg
  refine ⟨k, ⟨hk, ?_⟩, fun l hl ↦ hu l hl.1⟩
  apply (cancel_mono j).mp
  rw [Category.assoc, hilbertReindexedChartMap_global R I d m b hκ hm e,
    ← Category.assoc, hk, h]

end FLT.Mazur.HilbertChart

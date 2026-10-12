/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMonomialAmbientDecomposition
public import FLT.Mazur.GrassmannianAmbientComplementBaseChange

/-!
# Monomial ambient charts with a fixed complementary index

Reindexing the complement leaves the original monomial vectors unchanged.
The selected quotient coordinates are identities and the complementary
coordinates are evaluations in the entire original quotient algebra.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
universe u
variable (R I : Type u) [CommRing R] [Finite I] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)
  {κ : Type u} [Fintype κ]

/-- Use finite bounded monomial indices over the original base. -/
local instance reindexedMonomialsFintype : Fintype (BoundedHilbertMonomials I (d + 1)) :=
  Fintype.ofFinite _
/-- Use the actual unselected monomial indices. -/
local instance reindexedComplementFintype : Fintype (HilbertComplementMonomials I d m) :=
  Fintype.ofFinite _

/-- An actual decomposition of the original ambient with the prescribed global complement. -/
def hilbertReindexedAmbient (hm : Function.Injective m)
    (e : HilbertComplementMonomials I d m ≃ κ) :
    AmbientChartIndex R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d :=
  selectedAmbientChartWithComplement (boundedPolynomialBasis R I (d + 1))
    (hilbertSelectedEmbedding I d m hm) e

/-- The complementary monomials have exactly the ambient rank minus the quotient rank. -/
theorem hilbertComplementMonomials_card (hm : Function.Injective m) :
    Fintype.card (HilbertComplementMonomials I d m) =
      Fintype.card (BoundedHilbertMonomials I (d + 1)) - d := by
  exact (Fintype.card_congr
    (show HilbertComplementMonomials I d m ≃
      SelectedComplement (hilbertSelectedEmbedding I d m hm) from Equiv.refl _)).trans
        (selectedComplement_card (hilbertSelectedEmbedding I d m hm))

/-- Construct the complementary reindexing needed by the fixed global Grassmannian. -/
def hilbertComplementIndexEquiv (hm : Function.Injective m)
    (hκ : Fintype.card κ = Fintype.card (BoundedHilbertMonomials I (d + 1)) - d) :
    HilbertComplementMonomials I d m ≃ κ :=
  Fintype.equivOfCardEq ((hilbertComplementMonomials_card I d m hm).trans hκ.symm)

variable (S : Type u) [CommRing S] [Algebra R S]

omit [Finite I] in
/-- Reindexing preserves every selected pure tensor. -/
theorem hilbertReindexedAmbient_selected (hm : Function.Injective m)
    (e : HilbertComplementMonomials I d m ≃ κ) (j : Fin d) :
    ambientChartSelected (ambientChartBaseChange S (hilbertReindexedAmbient R I d m hm e))
        (Pi.basisFun S (Fin d) j) =
      1 ⊗ₜ[R] boundedPolynomialBasis R I (d + 1) (boundedSelectedMonomial I d m j) :=
  selectedAmbientChart_baseChange_basis S _ _ _ j

omit [Finite I] in
/-- Each reindexed complementary column is its original monomial pure tensor. -/
theorem hilbertReindexedAmbient_complement (hm : Function.Injective m)
    (e : HilbertComplementMonomials I d m ≃ κ) (j : κ) :
    ambientChartComplement (ambientChartBaseChange S (hilbertReindexedAmbient R I d m hm e))
        (Pi.basisFun S κ j) =
      1 ⊗ₜ[R] boundedPolynomialBasis R I (d + 1) (e.symm j).val :=
  selectedAmbientChart_baseChange_complement_basis S _ _ _ j

omit [Finite I] in
/-- A monomial quotient basis normalizes selected columns after arbitrary reindexing. -/
theorem hilbertReindexedAmbient_selected_coordinates (hm : Function.Injective m)
    (e : HilbertComplementMonomials I d m ≃ κ)
    (J : Ideal (MvPolynomial I S)) (v : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J))
    (hv : ∀ j, Ideal.Quotient.mk J (MvPolynomial.monomial (m j).val 1) = v j) :
    (hilbertAmbientCoordinates R S I J d v).comp
        (ambientChartSelected
          (ambientChartBaseChange S (hilbertReindexedAmbient R I d m hm e))) =
      LinearMap.id := by
  apply (Pi.basisFun S (Fin d)).ext
  intro j
  rw [LinearMap.comp_apply, hilbertReindexedAmbient_selected,
    hilbertAmbientCoordinates_monomial]
  change v.equivFun (Ideal.Quotient.mk J (MvPolynomial.monomial (m j).val 1)) = _
  rw [hv]
  classical
  ext k
  simp only [Module.Basis.equivFun_self, LinearMap.id_apply,
    Pi.basisFun_apply, Pi.single_apply, eq_comm]

omit [Finite I] in
/-- Complementary coordinates are computed in the full original polynomial quotient. -/
theorem hilbertReindexedAmbient_complement_coordinates (hm : Function.Injective m)
    (e : HilbertComplementMonomials I d m ≃ κ)
    (J : Ideal (MvPolynomial I S)) (v : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J))
    (j : κ) :
    hilbertAmbientCoordinates R S I J d v
        (ambientChartComplement
          (ambientChartBaseChange S (hilbertReindexedAmbient R I d m hm e))
          (Pi.basisFun S κ j)) =
      v.equivFun (Ideal.Quotient.mk J (MvPolynomial.monomial (e.symm j).val.val 1)) := by
  rw [hilbertReindexedAmbient_complement, hilbertAmbientCoordinates_monomial]

end FLT.Mazur.HilbertChart

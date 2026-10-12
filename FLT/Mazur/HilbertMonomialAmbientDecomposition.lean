/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertComplementCoordinateRing
public import FLT.Mazur.GrassmannianAmbientIndexBaseChange

/-!
# Original ambient decompositions for injective bounded monomial tuples

An injective selected tuple gives an actual decomposition of the original
bounded polynomial module, with precisely the complementary columns used in
the closed Hilbert chart map. Scalar extension preserves its original vectors.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)

/-- An injective monomial tuple stays injective in the larger ambient truncation. -/
def hilbertSelectedEmbedding (hm : Function.Injective m) :
    Fin d ↪ BoundedHilbertMonomials I (d + 1) where
  toFun := boundedSelectedMonomial I d m
  inj' := by
    intro i j h
    apply hm
    exact Subtype.ext
      (congrArg (fun n : BoundedHilbertMonomials I (d + 1) ↦ n.val) h)

instance hilbertComplementMonomials_finite [Finite I] :
    Finite (HilbertComplementMonomials I d m) :=
  inferInstanceAs (Finite {n : BoundedHilbertMonomials I (d + 1) //
    n ∉ Set.range (boundedSelectedMonomial I d m)})

variable [Finite I]
/-- Choose the finite original ambient monomial index. -/
local instance hilbertAmbientMonomialsFintype : Fintype (BoundedHilbertMonomials I (d + 1)) :=
  Fintype.ofFinite _
/-- Choose the finite complementary monomial index. -/
local instance hilbertAmbientComplementFintype : Fintype (HilbertComplementMonomials I d m) :=
  Fintype.ofFinite _

/-- The original-base Grassmannian chart with these selected and complementary monomials. -/
def hilbertMonomialAmbientIndex (hm : Function.Injective m) :
    AmbientChartIndex R (MvPolynomial.restrictTotalDegree I R (d + 1))
      (HilbertComplementMonomials I d m) d :=
  selectedAmbientChartWithComplement (boundedPolynomialBasis R I (d + 1))
    (hilbertSelectedEmbedding I d m hm) (Equiv.refl _)

/-- The selected ambient summand is exactly the original bounded monomial column map. -/
theorem hilbertMonomialAmbientIndex_selected (hm : Function.Injective m) :
    ambientChartSelected (hilbertMonomialAmbientIndex R I d m hm) =
      selectedColumnMap (fun j ↦
        boundedPolynomialBasis R I (d + 1) (boundedSelectedMonomial I d m j)) :=
  selectedAmbientChartWithComplement_selected (boundedPolynomialBasis R I (d + 1))
    (hilbertSelectedEmbedding I d m hm) (Equiv.refl _)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Every coefficient algebra sees the same selected original monomials as pure tensors. -/
theorem hilbertMonomialAmbientIndex_baseChange (hm : Function.Injective m) (j : Fin d) :
    ambientChartSelected
        (ambientChartBaseChange S (hilbertMonomialAmbientIndex R I d m hm))
        (Pi.basisFun S (Fin d) j) =
      1 ⊗ₜ[R] boundedPolynomialBasis R I (d + 1) (boundedSelectedMonomial I d m j) := by
  rw [ambientChartBaseChange_selected_basis, hilbertMonomialAmbientIndex_selected]
  simp only [selectedColumnMap, Module.Basis.constr_basis]

/-- A prescribed monomial quotient basis normalizes the selected ambient columns. -/
theorem hilbertMonomialAmbientIndex_coordinates (hm : Function.Injective m)
    (J : Ideal (MvPolynomial I S)) (v : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J))
    (hv : ∀ j, Ideal.Quotient.mk J (MvPolynomial.monomial (m j).val 1) = v j)
    (j : Fin d) :
    hilbertAmbientCoordinates R S I J d v
        (ambientChartSelected
          (ambientChartBaseChange S (hilbertMonomialAmbientIndex R I d m hm))
          (Pi.basisFun S (Fin d) j)) = Pi.basisFun S (Fin d) j := by
  rw [hilbertMonomialAmbientIndex_baseChange, hilbertAmbientCoordinates_monomial]
  change v.equivFun (Ideal.Quotient.mk J (MvPolynomial.monomial (m j).val 1)) = _
  rw [hv]
  classical
  ext k
  simp only [Module.Basis.equivFun_self, Pi.basisFun_apply, Pi.single_apply, eq_comm]

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertComplementPointCompatibility

/-!
# The closed Hilbert chart map agrees with the global Grassmannian morphism

The closed complementary-coordinate map followed by its actual Grassmannian
chart inclusion is the restriction of the global Hilbert Grassmannian map.
All morphisms use the original coefficient ring and the full universal ideal.
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
local notation "C" => ChartRing R I d w
local notation "c" => hilbertReindexedAmbient R I d m hm e

/-- Cache the original coefficient ring. -/
local instance complementSchemeCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the original chart ring. -/
local instance complementSchemeChartRing : CommRing C := inferInstance

/-- The actual closed chart map followed by the actual open chart inclusion is the global map. -/
theorem hilbertReindexedChartMap_global :
    hilbertReindexedChartMap R I d m e ≫
        ambientGrassmannianChart R (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d c =
      polynomialHilbertChartι R I d w ≫ hilbertGrassmannianMap R I d b hκ := by
  let f := (⟨hilbertReindexedChartMap R I d m e,
    hilbertReindexedChartMap_over R I d m e⟩ :
      {f : Spec (.of C) ⟶ splitChartScheme R κ d //
        f ≫ splitChartStructure R κ d = Spec.algebraMap R C})
  let P := ambientChartSchemePointEquiv c f
  have hp := hilbertReindexedChartMap_point R I d m hm e
  rw [hilbertGrassmannianMap_chartIdentity]
  change f.val ≫ _ = ambientClassifyingMap b _ hκ
  rw [← hp, ambientClassifyingMap_ofChart b hκ c P]
  change f.val ≫ _ = ((ambientChartSchemePointEquiv c).symm
    (ambientChartSchemePointEquiv c f)).val ≫ _
  rw [Equiv.symm_apply_apply]

variable [Finite I]
/-- Choose the native complementary monomial index. -/
local instance nativeComplementSchemeFintype : Fintype (HilbertComplementMonomials I d m) :=
  Fintype.ofFinite _

omit [Fintype κ] in
/-- The original complementary-coordinate map has the same global compatibility. -/
theorem hilbertComplementChartMap_global
    (hc : Fintype.card (HilbertComplementMonomials I d m) = Fintype.card ι - d) :
    hilbertComplementChartMap R I d m ≫
        ambientGrassmannianChart R (MvPolynomial.restrictTotalDegree I R (d + 1))
          (HilbertComplementMonomials I d m) d (hilbertMonomialAmbientIndex R I d m hm) =
      polynomialHilbertChartι R I d w ≫ hilbertGrassmannianMap R I d b hc := by
  exact hilbertReindexedChartMap_global R I d m b hc hm (Equiv.refl _)

end FLT.Mazur.HilbertChart

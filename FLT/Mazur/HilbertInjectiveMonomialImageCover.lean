/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertComplementSchemeCompatibility
public import FLT.Mazur.HilbertRepeatedMonomialChart

/-!
# Injective monomial charts cover the original Hilbert image

Empty repeated-tuple charts can be removed from the original bounded atlas.
The remaining actual closed chart maps cover the Hilbert image by the matching
original-base Grassmannian chart opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)

/-- The existing bounded Hilbert atlas restricted to its actual injective monomial tuples. -/
def injectiveBoundedPolynomialHilbertCover : (polynomialHilbertScheme R I d).OpenCover where
  I₀ := {m : Fin d → BoundedHilbertMonomials I d // Function.Injective m}
  X m := Spec (.of (ChartRing R I d (fun i ↦ MvPolynomial.monomial (m.val i).val 1)))
  f m := polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m.val i).val 1)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    obtain ⟨m, hm, y, hy⟩ := exists_injectiveBoundedPolynomialHilbertChart R I d x
    exact ⟨⟨m, hm⟩, y, hy⟩

instance [Finite I] : Finite (injectiveBoundedPolynomialHilbertCover R I d).I₀ :=
  inferInstanceAs (Finite {m : Fin d → BoundedHilbertMonomials I d // Function.Injective m})

instance (m : (injectiveBoundedPolynomialHilbertCover R I d).I₀) :
    IsAffine ((injectiveBoundedPolynomialHilbertCover R I d).X m) :=
  inferInstanceAs (IsAffine (Spec _))

variable [Finite I] {κ : Type u} [Fintype κ]
/-- Choose the finite original ambient monomial index. -/
local instance imageCoverMonomialFintype : Fintype (BoundedHilbertMonomials I (d + 1)) :=
  Fintype.ofFinite _
variable (hκ : Fintype.card κ = Fintype.card (BoundedHilbertMonomials I (d + 1)) - d)

/-- The Hilbert image is covered by matching original-base Grassmannian chart opens. -/
theorem hilbertGrassmannianMap_injectiveMonomial_cover (x : polynomialHilbertScheme R I d) :
    ∃ (m : Fin d → BoundedHilbertMonomials I d) (hm : Function.Injective m)
      (e : HilbertComplementMonomials I d m ≃ κ),
      hilbertGrassmannianMap R I d (boundedPolynomialBasis R I (d + 1)) hκ x ∈
        Set.range (ambientGrassmannianChart R
          (MvPolynomial.restrictTotalDegree I R (d + 1)) κ d
          (hilbertReindexedAmbient R I d m hm e)) := by
  obtain ⟨m, hm, y, hy⟩ := exists_injectiveBoundedPolynomialHilbertChart R I d x
  let e := hilbertComplementIndexEquiv I d m hm hκ
  refine ⟨m, hm, e, hilbertReindexedChartMap R I d m e y, ?_⟩
  rw [← hy]
  exact congrArg (fun f ↦ f y) (hilbertReindexedChartMap_global R I d m
    (boundedPolynomialBasis R I (d + 1)) hκ hm e)

end FLT.Mazur.HilbertChart

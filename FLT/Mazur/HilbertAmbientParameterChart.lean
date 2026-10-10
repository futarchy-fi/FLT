/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientClosedParameter

/-!
# Exact factorization of chart parameters through the ambient Hilbert scheme

Pulling the global closed equation ideal to any affine chart test recovers
its full coordinate ideal. Its vanishing is equivalent to containment of all
original ambient equations in the family's polynomial ideal.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R)) (w : Fin d → MvPolynomial I R)

/-- Cache coefficient rings for the global parameter restriction. -/
local instance ambientParameterCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache chart rings for the global parameter restriction. -/
local instance ambientParameterChartRing : CommRing (ChartRing R I d w) := inferInstance

variable (S : Type u) [CommRing S] [Algebra R S]
variable (f : ChartRing R I d w →ₐ[R] S)

/-- The global ambient equation sheaf restricts to the full image of the chart equation ideal. -/
theorem ambientHilbertIdeal_affineChart :
    (ambientHilbertIdeal R I d K).comap
        (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ polynomialHilbertChartι R I d w) =
      baseIdeal (.of S) ((ambientRelationsIdeal R I d w K).map f.toRingHom) := by
  rw [Scheme.IdealSheafData.comap_comp, ambientHilbertIdeal_chart]
  exact baseIdeal_comap_specMap _ _

/-- Vanishing of the full global closed equations is exactly actual ambient containment. -/
theorem ambientHilbertIdeal_affineChart_eq_bot_iff :
    (ambientHilbertIdeal R I d K).comap
        (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ polynomialHilbertChartι R I d w) = ⊥ ↔
      K.map (MvPolynomial.map (algebraMap R S)) ≤ pointIdeal R I d w f := by
  rw [ambientHilbertIdeal_affineChart]
  have hb : baseIdeal (.of S) (⊥ : Ideal S) = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp only [baseIdeal_top, Ideal.map_bot, Scheme.IdealSheafData.ideal_bot]
    rfl
  rw [← hb, (polynomialBaseIdeal_injective (.of S)).eq_iff,
    ← le_bot_iff, Ideal.map_le_iff_le_comap]
  exact ambientRelationsIdeal_le_ker_point_iff R I d w f K

end FLT.Mazur.HilbertChart

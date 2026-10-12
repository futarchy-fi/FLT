/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartPoints
public import FLT.Mazur.GrassmannianSplitChartCoordinates

/-!
# Recovering original ambient relations from normalized coordinates

A quotient map that is the identity on the selected summand is determined by
its complementary coordinates. Transporting the resulting split chart point
back to the original ambient recovers its entire relation submodule.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R M κ : Type*} [CommRing R] [AddCommGroup M] [Module R M] {d : ℕ}

/-- A normalized ambient quotient map is the split evaluation in the chosen decomposition. -/
theorem normalizedAmbientCoordinates_factor (i : AmbientChartIndex R M κ d)
    (q : M →ₗ[R] (Fin d → R))
    (hq : q.comp (ambientChartSelected i) = LinearMap.id) :
    q.comp i.toLinearMap = splitChartEvaluation (q.comp (ambientChartComplement i)) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hx : q (i (x, 0)) = x := LinearMap.congr_fun hq x
  change q (i (x, y)) = x + q (i (0, y))
  rw [show (x, y) = (x, 0) + (0, y) by simp, map_add, map_add, hx]

/-- Reconstructing normalized coordinates preserves every original ambient relation. -/
theorem normalizedAmbientCoordinates_relation (i : AmbientChartIndex R M κ d)
    (q : M →ₗ[R] (Fin d → R))
    (hq : q.comp (ambientChartSelected i) = LinearMap.id) :
    (ambientChartPointOfSplit i
      (splitChartOfCoordinates (q.comp (ambientChartComplement i)))).val.toSubmodule =
        q.ker := by
  ext x
  rw [ambientChartPointOfSplit, ambientTransportPoint_mem]
  change splitChartEvaluation (q.comp (ambientChartComplement i)) (i.symm x) = 0 ↔ q x = 0
  rw [← normalizedAmbientCoordinates_factor i q hq, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- A full quotient relation with normalized selected coordinates is the constructed chart point. -/
theorem normalizedAmbientCoordinates_point (i : AmbientChartIndex R M κ d)
    (q : M →ₗ[R] (Fin d → R))
    (hq : q.comp (ambientChartSelected i) = LinearMap.id)
    (N : Module.Grassmannian R M d) (hN : q.ker = N.toSubmodule) :
    (ambientChartPointOfSplit i
      (splitChartOfCoordinates (q.comp (ambientChartComplement i)))).val = N := by
  apply Module.Grassmannian.ext
  exact (normalizedAmbientCoordinates_relation i q hq).trans hN

/-- The original selected columns form a quotient basis, with no discarded relations. -/
theorem normalizedAmbientCoordinates_mem (i : AmbientChartIndex R M κ d)
    (q : M →ₗ[R] (Fin d → R))
    (hq : q.comp (ambientChartSelected i) = LinearMap.id)
    (N : Module.Grassmannian R M d) (hN : q.ker = N.toSubmodule) :
    Function.Bijective (N.toSubmodule.mkQ.comp (ambientChartSelected i)) := by
  rw [← normalizedAmbientCoordinates_point i q hq N hN]
  exact (ambientChartPointOfSplit i
    (splitChartOfCoordinates (q.comp (ambientChartComplement i)))).property

end FLT.Mazur.GrassmannianChart

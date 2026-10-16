/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioMap

/-!
# Full retained corrections with a fixed global smoothing

The roots on successive retained nodes use different local smoothing terms.
This construction lets their units act on one fixed target equation πq = τ,
without equating the local root smoothing with the global polygon smoothing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π τ q : R) (hq : π * q = τ)
  (V : (ChartRing π)ˣ)
local notation "C" => algebraMap R (ChartRing π)

include hq in
/-- An arbitrary full correction preserves the prescribed global target equation. -/
theorem retainedFixedSmoothing_relation :
    (C q * leftCoordinate π * (↑V⁻¹ : ChartRing π)) *
      (rightCoordinate π * (V : ChartRing π)) = C τ := by
  calc
    _ = C q * (leftCoordinate π * rightCoordinate π) *
        ((↑V⁻¹ : ChartRing π) * (V : ChartRing π)) := by ring
    _ = C q * C π := by rw [coordinate_relation, Units.inv_mul, mul_one]
    _ = C τ := by rw [← map_mul, mul_comm q π, hq]

/-- Corrected full coordinates with one chosen global smoothing, at any retained depth. -/
def retainedFixedSmoothingEvaluation : ChartRing τ →ₐ[R] ChartRing π :=
  evaluate τ (C q * leftCoordinate π * (↑V⁻¹ : ChartRing π))
    (rightCoordinate π * (V : ChartRing π)) (retainedFixedSmoothing_relation π τ q hq V)

/-- The outgoing coordinate retains the fixed global quotient and inverse correction. -/
theorem retainedFixedSmoothingEvaluation_left :
    retainedFixedSmoothingEvaluation π τ q hq V (leftCoordinate τ) =
      C q * leftCoordinate π * (↑V⁻¹ : ChartRing π) := evaluate_left ..

/-- The incoming coordinate retains the entire independently constructed correction. -/
theorem retainedFixedSmoothingEvaluation_right :
    retainedFixedSmoothingEvaluation π τ q hq V (rightCoordinate τ) =
      rightCoordinate π * (V : ChartRing π) := evaluate_right ..

/-- The whole retained node maps to the fixed global smoothing. -/
def retainedFixedSmoothingChart : chart R π ⟶ chart R τ :=
  Spec.map (CommRingCat.ofHom (retainedFixedSmoothingEvaluation π τ q hq V).toRingHom)

/-- The fixed-smoothing comparison retains the original coefficient structure. -/
@[reassoc] theorem retainedFixedSmoothingChart_structure :
    retainedFixedSmoothingChart π τ q hq V ≫ chartStructure R τ = chartStructure R π := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (RingHom.ext (retainedFixedSmoothingEvaluation π τ q hq V).commutes)

variable (W : WeierstrassCurve R) (s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
  (d : R) (hd : s = π * d)

/-- The original first-retained evaluation is exactly this fixed-smoothing construction. -/
theorem retainedFactorRatioEvaluation_eq_fixed :
    retainedFactorRatioEvaluation W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd =
      retainedFixedSmoothingEvaluation π (initialTangentSmoothing W ha s)
        ((↑(zeroInitialTangentUnit W ha)⁻¹ : R) ^ 2 * d)
        (by rw [initialTangentSmoothing, hd]; ring)
        (retainedFactorCorrectionUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6) := rfl

end FLT.Mazur.WeierstrassModificationX

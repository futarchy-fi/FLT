/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactor
public import FLT.Mazur.WeierstrassModificationXInitialMobiusNormalization

/-!
# A full retained-node comparison with the exact corrected smoothing

The right coordinate uses the square of the original tangent unit divided by
the square of the constructed opposite factor. The left coordinate absorbs
the actual quotient s/π, retaining τ = a₁⁻² s for arbitrary starting thickness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "B" => ChartRing π
local notation "C" => algebraMap R B
local notation "a" => zeroInitialTangentUnit W ha
local notation "U" => retainedOppositeUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6

/-- The full squared-factor correction is a unit on the entire retained node. -/
def retainedFactorCorrectionUnit : Bˣ := Units.map C a ^ 2 * (U)⁻¹ ^ 2
local notation "v" => retainedFactorCorrectionUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "τ" => initialTangentSmoothing W ha s
variable (d : R) (hd : s = π * d)
local notation "q" => (↑a⁻¹ : R) ^ 2 * d
attribute [local irreducible] retainedFactorCorrectionUnit

include hd in
/-- The full corrected coordinates multiply to the exact normalized smoothing. -/
theorem retainedFactorRatio_relation :
    (C q * leftCoordinate π * (↑(v)⁻¹ : B)) * (rightCoordinate π * (v : B)) = C τ := by
  calc
    _ = C q * (leftCoordinate π * rightCoordinate π) * ((↑(v)⁻¹ : B) * (v : B)) := by
      ring
    _ = C q * C π := by rw [coordinate_relation, Units.inv_mul, mul_one]
    _ = C τ := by
      rw [← map_mul]
      congr 1
      rw [initialTangentSmoothing, hd]
      ring

/-- The complete original retained algebra maps to the polygon algebra with actual smoothing. -/
def retainedFactorRatioEvaluation : ChartRing τ →ₐ[R] B :=
  evaluate τ (C q * leftCoordinate π * (↑(v)⁻¹ : B)) (rightCoordinate π * (v : B))
    (retainedFactorRatio_relation W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd)
local notation "F" => retainedFactorRatioEvaluation W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd

/-- The left coordinate keeps both the full correction and the actual extra thickness. -/
theorem retainedFactorRatioEvaluation_left :
    F (leftCoordinate τ) = C q * leftCoordinate π * (↑(v)⁻¹ : B) :=
  evaluate_left ..

/-- The right coordinate keeps the complete square of the opposite-factor correction. -/
theorem retainedFactorRatioEvaluation_right :
    F (rightCoordinate τ) = rightCoordinate π * (v : B) :=
  evaluate_right ..

/-- The full original retained node has a constructed comparison with the corrected node. -/
def retainedFactorRatioChart : chart R π ⟶ chart R τ :=
  Spec.map (CommRingCat.ofHom (F).toRingHom)

/-- The full retained comparison preserves every original coefficient. -/
@[reassoc] theorem retainedFactorRatioChart_structure :
    retainedFactorRatioChart W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd ≫
      chartStructure R τ = chartStructure R π := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (F).commutes)

end FLT.Mazur.WeierstrassModificationX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticNodeChart
public import FLT.Mazur.WeierstrassSuccessivePolygonRestrictionSquare

/-!
# Original restriction maps between arithmetic node charts

The polygon and three-coordinate chart arrows use the actual original
quotient restriction. Compatibility of their node comparisons is separate work.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R] (π : R) (m : ℕ)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "q₀" => algebraMap R Q₀
local notation "q₁" => algebraMap R Q₁
local notation "f" => (AlgHom.toRingHom (restriction R π m))

/-- The original arithmetic restriction carries the parameter ideal into itself. -/
theorem arithmeticParameterIdeal_restriction :
    ideal Q₁ (parameter R π (m + 1)) ≤ (ideal Q₀ (parameter R π m)).comap f := by
  apply Ideal.span_le.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change restriction R π m (parameter R π (m + 1)) ∈ ideal Q₀ (parameter R π m)
  rw [restriction_parameter]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The original polygon tensor coefficient map between consecutive arithmetic orders. -/
def arithmeticPolygonNodeRestriction :
    Spec (.of (PolygonSmoothing.ChartRing (parameter R π m))) ⟶
      Spec (.of (PolygonSmoothing.ChartRing (parameter R π (m + 1)))) := by
  letI := (f).toAlgebra
  exact PolygonSmoothing.chartCoefficient Q₁ Q₀ (parameter R π (m + 1))

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The three-coordinate chart restriction uses the original quotient ring homomorphism. -/
def arithmeticSuccessiveRestriction :
    Spec (.of (ExtendedCoordinate W s π b3 b4 b6 Q₀)) ⟶
      Spec (.of (ExtendedCoordinate W s π b3 b4 b6 Q₁)) :=
  Spec.map (CommRingCat.ofHom
    (coefficientRingMap f (W.map q₁) (q₁ s) (q₁ π) (q₁ b3) (q₁ b4) (q₁ b6)))

end FLT.Mazur.WeierstrassSuccessiveX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureAddition
public import FLT.Mazur.CartesianMonoGroup

/-!
# The actual finite subgroup closure is a commutative group in good reduction

The constructed zero, addition and negation preserve the original closed
immersion into the integral cubic. Cancellation proves all group laws.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The actual ambient closed immersion is a monomorphism over the valuation ring. -/
instance closureOverToCurve_mono : Mono (closureOverToCurve A W H 1 2) := by
  have : Mono (closureOverToCurve A W H 1 2).left := by
    change Mono (closureToCurve A W H 1 2)
    infer_instance
  exact Over.mono_of_mono_left _

/-- The descended inverse preserves the original ambient inverse in the slice category. -/
@[reassoc] theorem closureOverNegation_toCurve :
    closureOverNegation A W H ≫ closureOverToCurve A W H 1 2 =
      closureOverToCurve A W H 1 2 ≫ integralCurveOverNegation W := by
  apply Over.OverMorphism.ext
  exact closureNegation_toCurve A W H

variable [IsDedekindDomain A]

/-- The constructed addition preserves the actual ambient multiplication over the base. -/
@[reassoc] theorem closureOverAddition_toCurve (hΔ : IsUnit W.Δ) :
    closureOverAddition A W H hΔ ≫ closureOverToCurve A W H 1 2 =
      (closureOverToCurve A W H 1 2 ⊗ₘ closureOverToCurve A W H 1 2) ≫
        integralCurveOverAddition W hΔ := by
  apply Over.OverMorphism.ext
  exact closureAddition_toCurve A W H hΔ

/-- The original closure carries the restricted commutative group operations. -/
@[instance_reducible] def closureCommGrpObj (hΔ : IsUnit W.Δ) :
    CommGrpObj (Over.mk (closureToBase A W H 1 2)) := by
  letI := integralCurveCommGrpObj W hΔ
  exact CartesianMonoGroup.commGrpObj (closureOverToCurve A W H 1 2)
    (closureOverZero A W H) (closureOverAddition A W H hΔ) (closureOverNegation A W H)
    (closureOverZero_toCurve A W H) (closureOverAddition_toCurve A W H hΔ)
    (closureOverNegation_toCurve A W H)

/-- The actual finite flat closure, bundled as a commutative group scheme. -/
def closureGroup (hΔ : IsUnit W.Δ) : CommGrp (Over (Spec (.of A))) := by
  letI := closureCommGrpObj A W H hΔ
  exact ⟨Over.mk (closureToBase A W H 1 2)⟩

/-- The bundled group has precisely the original closure as its carrier. -/
theorem closureGroup_carrier (hΔ : IsUnit W.Δ) :
    (closureGroup A W H hΔ).X = Over.mk (closureToBase A W H 1 2) := rfl

/-- The actual ambient immersion preserves the unit and multiplication. -/
instance closureGroup_inclusion_isMonHom (hΔ : IsUnit W.Δ) :
    letI := closureCommGrpObj A W H hΔ
    letI := integralCurveCommGrpObj W hΔ
    IsMonHom (closureOverToCurve A W H 1 2) := by
  let _ := closureCommGrpObj A W H hΔ
  let _ := integralCurveCommGrpObj W hΔ
  exact ⟨closureOverZero_toCurve A W H, closureOverAddition_toCurve A W H hΔ⟩

/-- The ambient closed immersion as a morphism of actual commutative group schemes. -/
def closureGroupInclusion (hΔ : IsUnit W.Δ) :
    closureGroup A W H hΔ ⟶ integralCurveGroup W hΔ :=
  ⟨Grp.ofHom (closureOverToCurve A W H 1 2)⟩

end FLT.Mazur.EllipticSubgroupChart

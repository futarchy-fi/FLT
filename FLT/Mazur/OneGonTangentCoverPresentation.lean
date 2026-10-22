/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonTangentCoverNormalForm
public import FLT.Mazur.OneGonTangentEtaleCover
public import FLT.Mazur.WeierstrassIntegralBaseChange

/-!
# Whole nodal deformation presentations on an etale cover

The nonsplit original cubic becomes a full arithmetic generalized curve on
its actual quadratic etale cover. The underlying cubic comparison is with the
categorical pullback of the original curve, not just a fresh coefficient model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
open WeierstrassIntegralChart
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "f" => algebraMap R S
local notation "J" => I.map f

/-- The cover's coefficient cubic is the actual categorical pullback of the original cubic. -/
def tangentCubicBaseChangeIso : integralCurveOver (W.map f) ≅
    (Over.pullback (nodeTangentCover W)).obj (integralCurveOver W) :=
  Over.isoMk (integralCurveCoefficientBaseChangeIso W)
    (integralCurveCoefficientBaseChangeIso_snd W)

/-- The comparison projects to the original coefficient morphism. -/
@[reassoc] theorem tangentCubicBaseChangeIso_fst :
    (tangentCubicBaseChangeIso W).hom.left ≫
      Limits.pullback.fst (integralCurveStructure W) (nodeTangentCover W) =
        integralCoefficientMorphism W :=
  integralCurveCoefficientBaseChangeIso_fst W

/-- Whole arithmetic presentations exist on the original etale cover, retaining the reduction. -/
theorem tangentCover_full_presentation (hI : IsNilpotent I) (hb : IsUnit W.b₂)
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    ∃ (C : VariableChange S) (t : S) (ht : IsUnit (1 + 432 * t))
      (he : C • W.map f = OneGonSmoothing.equation t),
      C.map (Ideal.Quotient.mk J) = tangentCoverResidualChange W I hb ∧ t ∈ J ∧
        Nonempty (curveOfNormalForm (W.map f) t C he ht ≅
          ArithmeticOneGonParameter.universalCurve.baseChange
            (ArithmeticOneGonParameter.parameterMap t ht)) :=
  residual_full_presentation (W.map f) J (nilpotent_map I hI f)
    (tangentCoverResidualChange W I hb)
    (tangentCoverResidualChange_equation W I hb h₃ h₄ h₆)

/-- The whole original cubic, pulled back on an etale surjection, has a one-gon presentation. -/
theorem tangentCover_cubic_presentation [Nontrivial R]
    (hI : IsNilpotent I) (hb : IsUnit W.b₂)
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    Etale (nodeTangentCover W) ∧ Surjective (nodeTangentCover W) ∧
      ∃ t : S, t ∈ J ∧ IsUnit (1 + 432 * t) ∧
        Nonempty (OneGonSmoothing.family t ≅
          (Over.pullback (nodeTangentCover W)).obj (integralCurveOver W)) := by
  obtain ⟨C, t, he, _, ht, hu⟩ := tangentCover_normalForm W I hI hb h₃ h₄ h₆
  exact ⟨(tangentCover_etale_surjective W hb).1, (tangentCover_etale_surjective W hb).2,
    t, ht, hu, ⟨integralVariableChangeOverIso (W.map f) (OneGonSmoothing.equation t) C he ≪≫
      tangentCubicBaseChangeIso W⟩⟩

end FLT.Mazur.OneGonInfinitesimal

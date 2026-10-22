/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSingularTranslation
public import FLT.Mazur.OneGonTangentCoverPresentation

/-!
# Etale presentations at arbitrary original residual nodes

Center the given residual singular point and use its actual tangent cover.
The final admissible change acts on the original uncentered equation.
All constructions allow nilpotents and residue characteristics two and three.
-/

@[expose] public noncomputable section
open WeierstrassCurve AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)
  (hI : IsNilpotent I) (x y : R)
local notation "V" => centeredEquation W x y
local notation "A" => AdjoinRoot (nodeTangentPolynomial V)
local notation "f" => algebraMap R A
local notation "q" => Ideal.Quotient.mk I

include hI

/-- A residual ordinary node anywhere on the affine cubic gives an original normal form. -/
theorem residualSingularCover_normalForm
    (he : (W.map q).toAffine.Equation (q x) (q y))
    (hx : (W.map q).toAffine.polynomialX.evalEval (q x) (q y) = 0)
    (hy : (W.map q).toAffine.polynomialY.evalEval (q x) (q y) = 0)
    (hd : IsUnit (q (W.b₂ + 12 * x))) :
    ∃ (C : VariableChange A) (t : A), C • W.map f = OneGonSmoothing.equation t ∧
      t ∈ I.map f ∧ IsUnit (1 + 432 * t) := by
  obtain ⟨h₃, h₄, h₆⟩ := centeredEquation_residual W I x y he hx hy
  have hb : IsUnit (V).b₂ := by
    rw [centeredEquation_b₂]
    exact hI.isUnit_quotient_mk_iff.mp hd
  obtain ⟨D, t, ht, _, hi, hu⟩ := tangentCover_normalForm V I hI hb h₃ h₄ h₆
  refine ⟨D * (centerChange x y).map f, t, ?_, hi, hu⟩
  rw [mul_smul, map_variableChange]
  exact ht

/-- The same original residual-node cover is an etale surjection. -/
theorem residualSingularCover_etale_surjective [Nontrivial R]
    (hd : IsUnit (q (W.b₂ + 12 * x))) :
    Etale (nodeTangentCover V) ∧ Surjective (nodeTangentCover V) := by
  apply tangentCover_etale_surjective
  rw [centeredEquation_b₂]
  exact hI.isUnit_quotient_mk_iff.mp hd

/-- The complete original uncentered cubic receives its intrinsic generalized presentation. -/
theorem residualSingularCover_full_presentation
    (he : (W.map q).toAffine.Equation (q x) (q y))
    (hx : (W.map q).toAffine.polynomialX.evalEval (q x) (q y) = 0)
    (hy : (W.map q).toAffine.polynomialY.evalEval (q x) (q y) = 0)
    (hd : IsUnit (q (W.b₂ + 12 * x))) :
    ∃ (C : VariableChange A) (t : A) (ht : IsUnit (1 + 432 * t))
      (heq : C • W.map f = OneGonSmoothing.equation t), t ∈ I.map f ∧
        Nonempty (curveOfNormalForm (W.map f) t C heq ht ≅
          ArithmeticOneGonParameter.universalCurve.baseChange
            (ArithmeticOneGonParameter.parameterMap t ht)) := by
  obtain ⟨C, t, heq, hi, ht⟩ := residualSingularCover_normalForm W I hI x y he hx hy hd
  exact ⟨C, t, ht, heq, hi, ⟨(generalizedNormalFormIso (W.map f) t C heq ht).symm ≪≫
    ArithmeticOneGonParameter.specializationIso t ht⟩⟩

end FLT.Mazur.OneGonInfinitesimal

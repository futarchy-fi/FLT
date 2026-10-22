/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonResidualSingularCover

/-!
# Original nodal deformations admit etale arithmetic presentations

Only a singular point on the original nilpotent reduction is specified.
Lift its coordinates, construct the quadratic etale coefficient cover, and
normalize the original equation there. No lift or tangent root is assumed.
-/

@[expose] public noncomputable section
open WeierstrassCurve AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type} [CommRing R] [Nontrivial R]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : IsNilpotent I)
  (x₀ y₀ : R ⧸ I)
local notation "q" => Ideal.Quotient.mk I

include hI

/-- A residual ordinary node gives a finite etale rank-two cover and a true normal form. -/
theorem exists_residualNode_normalForm
    (he : (W.map q).toAffine.Equation x₀ y₀)
    (hx : (W.map q).toAffine.polynomialX.evalEval x₀ y₀ = 0)
    (hy : (W.map q).toAffine.polynomialY.evalEval x₀ y₀ = 0)
    (hd : IsUnit (q W.b₂ + 12 * x₀)) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧ (algebraMap R A).FaithfullyFlat ∧
        Module.finrank R A = 2 ∧ ∃ (C : VariableChange A) (t : A),
          C • W.map (algebraMap R A) = OneGonSmoothing.equation t ∧
            t ∈ I.map (algebraMap R A) ∧ IsUnit (1 + 432 * t) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x₀
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y₀
  have hd' : IsUnit (q (W.b₂ + 12 * x)) := by
    simpa only [map_add, map_mul, map_ofNat] using hd
  have hb : IsUnit (centeredEquation W x y).b₂ := by
    rw [centeredEquation_b₂]
    exact hI.isUnit_quotient_mk_iff.mp hd'
  refine ⟨AdjoinRoot (nodeTangentPolynomial (centeredEquation W x y)),
    inferInstance, inferInstance, (nodeTangentPolynomial_monic _).finite_adjoinRoot,
    tangentAlgebra_etale _ hb, nodeTangentAlgebra_faithfullyFlat _,
    nodeTangentAlgebra_finrank _, ?_⟩
  exact residualSingularCover_normalForm W I hI x y he hx hy hd'

/-- The same constructed cover gives a full arithmetic generalized-curve presentation. -/
theorem exists_residualNode_full_presentation
    (he : (W.map q).toAffine.Equation x₀ y₀)
    (hx : (W.map q).toAffine.polynomialX.evalEval x₀ y₀ = 0)
    (hy : (W.map q).toAffine.polynomialY.evalEval x₀ y₀ = 0)
    (hd : IsUnit (q W.b₂ + 12 * x₀)) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧ (algebraMap R A).FaithfullyFlat ∧
        Module.finrank R A = 2 ∧
          ∃ (C : VariableChange A) (t : A) (ht : IsUnit (1 + 432 * t))
            (heq : C • W.map (algebraMap R A) = OneGonSmoothing.equation t),
            t ∈ I.map (algebraMap R A) ∧
              Nonempty (curveOfNormalForm (W.map (algebraMap R A)) t C heq ht ≅
                ArithmeticOneGonParameter.universalCurve.baseChange
                  (ArithmeticOneGonParameter.parameterMap t ht)) := by
  obtain ⟨A, hA, hRA, hfin, het, hff, hr, C, t, heq, hi, ht⟩ :=
    exists_residualNode_normalForm W I hI x₀ y₀ he hx hy hd
  exact ⟨A, hA, hRA, hfin, het, hff, hr, C, t, ht, heq, hi,
    ⟨(generalizedNormalFormIso (W.map (algebraMap R A)) t C heq ht).symm ≪≫
      ArithmeticOneGonParameter.specializationIso t ht⟩⟩

end FLT.Mazur.OneGonInfinitesimal

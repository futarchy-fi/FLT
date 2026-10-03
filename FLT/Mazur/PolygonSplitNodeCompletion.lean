/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesQuotientCompletion
public import FLT.Mazur.PolygonNodeCompletionCriterion
public import FLT.Mazur.AdicCompletionAlgEquiv

/-!
# The completed split polygon node

The equation `xy` presents the actual equalizer ring. Completing this
presentation gives the specified ordinary-double-point power-series model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonSplitNodeCompletion
open PolygonNodePresentation PolygonNodeEqualizer FCurve.CurveNode
variable (K : Type*) [Field K]

theorem evaluation (p : MvPolynomial (Fin 2) K) :
    aEval (aPresent p) = MvPolynomial.constantCoeff p := by
  have h : (aEval (R := K)).toRingHom.comp aPresent.toRingHom =
      MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i <;> simp [aEval]
  exact RingHom.congr_fun h p

theorem evaluation_ideal :
    RingHom.ker (aEval (R := K)).toRingHom =
      ((MvPolynomial.idealOfVars (Fin 2) K).map (Ideal.Quotient.mk aRelation)).map
        (aQuotientEquiv (R := K)).toRingHom := by
  rw [Ideal.map_map]
  have h : (aQuotientEquiv (R := K)).toRingHom.comp (Ideal.Quotient.mk aRelation) =
      aPresent.toRingHom := by
    apply RingHom.ext
    intro p
    simp [aQuotientEquiv]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk aPresent_surjective p
  rw [h]
  exact (PowerSeriesQuotientCompletion.map_idealOfVars aPresent aEval
    aPresent_surjective (evaluation K)).symm

/-- The completed affine split node is the formal ordinary double point. -/
def equivalence :
    AdicCompletion (RingHom.ker (aEval (R := K)).toRingHom) (A (R := K)) ≃ₐ[K]
      Model K := by
  let e := (AdicCompletionAlgEquiv.equivalence (aQuotientEquiv (R := K))
    ((MvPolynomial.idealOfVars (Fin 2) K).map (Ideal.Quotient.mk aRelation))
    (RingHom.ker (aEval (R := K)).toRingHom) (evaluation_ideal K)).symm
  let f := (PowerSeriesQuotientCompletion.equivalence
    (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) K)
    (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))).symm
  have h : Ideal.span {((MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K)} = equationIdeal K := by
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, equationIdeal]
  exact e.trans (f.trans (Ideal.quotientEquivAlgOfEq K h))

theorem atWorstNodes : AtWorstNodes (aToBase K) :=
  (PolygonNodeCompletionCriterion.split_node K).mpr ⟨equivalence K⟩
end FLT.Mazur.PolygonSplitNodeCompletion

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesQuotientCompletion
public import FLT.Mazur.PolygonNodeCompletionCriterion
public import FLT.Mazur.AdicCompletionAlgEquiv
public import FLT.Mazur.OneGonFormalCoordinates

/-!
# The completed one-gon node

The completed polynomial presentation of the one-gon is transformed
by formal coordinate automorphisms into the split ordinary double point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonOneGonCompletion
open PolygonNodePresentation PolygonNodeEqualizer FCurve.CurveNode
variable (K : Type*) [Field K]

theorem evaluation (p : MvPolynomial (Fin 2) K) :
    bEval (bPresent p) = MvPolynomial.constantCoeff p := by
  have h : (bEval (R := K)).toRingHom.comp bPresent.toRingHom =
      MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i <;> simp [bEval, u, v]
  exact RingHom.congr_fun h p

theorem evaluation_ideal :
    RingHom.ker (bEval (R := K)).toRingHom =
      ((MvPolynomial.idealOfVars (Fin 2) K).map (Ideal.Quotient.mk bRelation)).map
        (bQuotientEquiv (K := K)).toRingHom := by
  rw [Ideal.map_map]
  have h : (bQuotientEquiv (K := K)).toRingHom.comp (Ideal.Quotient.mk bRelation) =
      bPresent.toRingHom := by
    apply RingHom.ext
    intro p
    simp only [RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgHom.toRingHom_eq_coe]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk bPresent_surjective p
  rw [h]
  exact (PowerSeriesQuotientCompletion.map_idealOfVars bPresent bEval
    bPresent_surjective (evaluation K)).symm

theorem equation_ne_zero : bEquation (R := K) ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.aeval (![0, 1] : Fin 2 → K)) h
  simp only [bEquation, map_sub, map_mul, map_pow, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, zero_mul,
    zero_pow (show 3 ≠ 0 by decide), sub_zero, map_zero] at h'
  exact one_ne_zero h'

theorem equation_coe : ((bEquation (R := K)) : MvPowerSeries (Fin 2) K) =
    OneGonFormalCoordinates.cubic K := by
  have hs (p q : MvPolynomial (Fin 2) K) :
      ((p - q : MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K) =
        (p : MvPowerSeries (Fin 2) K) - q := by
    ext d
    exact map_sub (MvPolynomial.coeffAddMonoidHom d) p q
  simp only [bEquation, hs, MvPolynomial.coe_pow, MvPolynomial.coe_mul,
    MvPolynomial.coe_X, OneGonFormalCoordinates.cubic]

theorem formal_ideal : equationIdeal K =
    (Ideal.span {((bEquation (R := K)) : MvPowerSeries (Fin 2) K)}).map
      (OneGonFormalCoordinates.equivalence K).toRingHom := by
  rw [Ideal.map_span, Set.image_singleton, equation_coe]
  change equationIdeal K = Ideal.span {(OneGonFormalCoordinates.equivalence K
    (OneGonFormalCoordinates.cubic K))}
  rw [OneGonFormalCoordinates.equation]
  rfl

/-- The completed affine one-gon node is the formal ordinary double point. -/
def equivalence :
    AdicCompletion (RingHom.ker (bEval (R := K)).toRingHom) (B (R := K)) ≃ₐ[K]
      Model K :=
  (AdicCompletionAlgEquiv.equivalence (bQuotientEquiv (K := K))
    ((MvPolynomial.idealOfVars (Fin 2) K).map (Ideal.Quotient.mk bRelation))
    (RingHom.ker (bEval (R := K)).toRingHom) (evaluation_ideal K)).symm.trans
      ((PowerSeriesQuotientCompletion.equivalence (bEquation (R := K))
        (equation_ne_zero K)).symm.trans
          (Ideal.quotientEquivAlg _ _ (OneGonFormalCoordinates.equivalence K) (formal_ideal K)))

theorem atWorstNodes : AtWorstNodes (bToBase K) :=
  (PolygonNodeCompletionCriterion.one_gon K).mpr ⟨equivalence K⟩
end FLT.Mazur.PolygonOneGonCompletion

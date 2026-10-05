/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalEvaluationAddition
public import FLT.Mazur.EllipticLocalChartPoint

/-!
# Convergent formal addition is actual addition on E₁

The convergent two-variable series computes the parameter of the actual sum,
including equal inputs. The comparison is made with the projective group law,
not with a group operation postulated on formal parameters.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]
variable {σ : Type*} [Finite σ] (a : σ → A) (ha : ∀ i, a i ∈ maximalIdeal A)

/-- The evaluated formal representative is the actual convergent chart representative. -/
theorem localMvEvaluation_representative {t : MvPowerSeries σ A}
    (ht : t.constantCoeff = 0) :
    ((algebraMap A K).comp (localMvEvaluation A a ha)) ∘ FormalInfinity.representative W t =
      (algebraMap A K) ∘ ![localMvEvaluation A a ha t, -1,
        infinityEvaluation A W (localMvEvaluation A a ha t) (localMvEvaluation_mem A a ha ht)] := by
  simp only [FormalInfinity.representative, comp_fin3, RingHom.comp_apply, map_neg,
    map_one, localMvEvaluation_coordinate A a ha W ht]

/-- Evaluating any formal sum agrees with addition of the corresponding actual E₁ points. -/
theorem localE1Point_evaluation_add {t v : MvPowerSeries σ A}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    localE1Point A W (localMvEvaluation A a ha (FormalInfinity.add W t v))
      (localMvEvaluation_mem A a ha (FormalInfinity.constantCoeff_add W ht hv)) =
      localE1Point A W (localMvEvaluation A a ha t) (localMvEvaluation_mem A a ha ht) +
        localE1Point A W (localMvEvaluation A a ha v) (localMvEvaluation_mem A a ha hv) := by
  let f := (algebraMap A K).comp (localMvEvaluation A a ha)
  have hc : (FormalInfinity.curve W).map f = W.map (algebraMap A K) := by
    rw [FormalInfinity.curve, WeierstrassCurve.map_map]
    congr 1
    apply RingHom.ext
    intro c
    simp [f]
  have h := congrArg Point.point (FormalInfinity.evaluationPoint_add W f ht hv)
  change (⟦f ∘ FormalInfinity.representative W (FormalInfinity.add W t v)⟧ : PointClass K) =
    ((FormalInfinity.curve W).map f).toProjective.addMap
      ⟦f ∘ FormalInfinity.representative W t⟧ ⟦f ∘ FormalInfinity.representative W v⟧ at h
  rw [hc] at h
  rw [localMvEvaluation_representative A W a ha (FormalInfinity.constantCoeff_add W ht hv),
    localMvEvaluation_representative A W a ha ht,
    localMvEvaluation_representative A W a ha hv] at h
  apply Subtype.ext
  exact Point.ext h

/-- The convergent addition series computes the actual E₁ sum parameter. -/
theorem infinityParameter_add (P Q : ellipticE1 A W) :
    infinityParameter A W (P + Q) =
      localMvEvaluation A ![infinityParameter A W P, infinityParameter A W Q]
        (by intro i; fin_cases i <;> apply infinityParameter_mem)
        (FormalInfinity.additionSeries W) := by
  let a := ![infinityParameter A W P, infinityParameter A W Q]
  have ha : ∀ i : Fin 2, a i ∈ maximalIdeal A := by
    intro i
    fin_cases i <;> apply infinityParameter_mem
  have h := localE1Point_evaluation_add A W a ha
    (t := MvPowerSeries.X 0) (v := MvPowerSeries.X 1) (by simp) (by simp)
  have hp := congrArg (infinityParameter A W) h
  simpa only [infinityParameter_localE1Point, localMvEvaluation_X,
    a, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    localE1Point_infinityParameter, FormalInfinity.additionSeries] using hp.symm

end FLT.Mazur

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesGrading

/-!
# Mapping the actual degree-zero Rees localization to the fraction chart

Evaluation at 1/f sends the original degree-one denominator f*T to one.
It therefore induces a map on the actual homogeneous localization. The map
retains all homogeneous fractions and surjects onto the original fraction chart.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type*} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)

/-- The original Rees evaluation with its actual fraction-image codomain. -/
def evaluationToChart : reesAlgebra I →ₐ[A] BlowupFractionChart.chart I f :=
  (BlowupFractionChart.evaluation I f).rangeRestrict

/-- Evaluation sends the actual homogeneous denominator f*T to one. -/
theorem evaluation_generator :
    (evaluationToChart I f) (generator I f hf) = 1 := by
  apply Subtype.ext
  change BlowupFractionChart.evaluation I f
    ⟨Polynomial.monomial 1 f, _⟩ = 1
  rw [BlowupFractionChart.evaluation_degreeOne I f f hf, IsLocalization.Away.mul_invSelf]

/-- Evaluation extends over the full localization of the original Rees algebra. -/
def localizationEvaluation : Localization.Away (generator I f hf) →ₐ[A]
    BlowupFractionChart.chart I f :=
  IsLocalization.Away.liftAlgHom (generator I f hf)
    (f := (evaluationToChart I f))
    (by rw [evaluation_generator]; exact isUnit_one)

/-- Restrict the evaluation map to the actual homogeneous degree-zero localization. -/
def degreeZeroToFraction : DegreeZeroChart I f hf →+* BlowupFractionChart.chart I f :=
  (localizationEvaluation I f hf).toRingHom.comp
    (algebraMap (DegreeZeroChart I f hf) (Localization.Away (generator I f hf)))

/-- The localization map retains the original evaluation on a homogeneous numerator. -/
theorem localizationEvaluation_mk (p : reesAlgebra I) (n : ℕ) :
    localizationEvaluation I f hf (Localization.mk p ⟨generator I f hf ^ n, n, rfl⟩) =
      (evaluationToChart I f) p := by
  have he := Localization.awayLift_mk
    (evaluationToChart I f).toRingHom
    (generator I f hf) p 1 (by rw [mul_one]; exact evaluation_generator I f hf) n
  simpa only [localizationEvaluation, IsLocalization.Away.liftAlgHom_apply,
    Localization.awayLift, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    one_pow, mul_one] using he

/-- Every homogeneous fraction has its expected actual fraction-chart value. -/
@[simp] theorem degreeZeroToFraction_homogeneousFraction (n : ℕ) (a : ↥(I ^ n)) :
    degreeZeroToFraction I f hf (homogeneousFraction I f hf n a) =
      (evaluationToChart I f) (monomialMap I n a) := by
  change localizationEvaluation I f hf
    (HomogeneousLocalization.val (homogeneousFraction I f hf n a)) = _
  rw [homogeneousFraction, HomogeneousLocalization.Away.val_mk, localizationEvaluation_mk]

/-- The map evaluates a homogeneous numerator a*T^n as a/f^n. -/
theorem degreeZeroToFraction_coe (n : ℕ) (a : ↥(I ^ n)) :
    (degreeZeroToFraction I f hf (homogeneousFraction I f hf n a) : Localization.Away f) =
      algebraMap A (Localization.Away f) a * IsLocalization.Away.invSelf f ^ n := by
  rw [degreeZeroToFraction_homogeneousFraction]
  change aeval (IsLocalization.Away.invSelf f) (Polynomial.monomial n (a : A)) = _
  exact aeval_monomial _

/-- Every element of the actual fraction chart comes from the degree-zero localization. -/
theorem degreeZeroToFraction_surjective : Function.Surjective (degreeZeroToFraction I f hf) := by
  intro z
  obtain ⟨p, hp⟩ := (BlowupFractionChart.evaluation I f).rangeRestrict_surjective z
  refine ⟨∑ n ∈ (p : A[X]).support,
    homogeneousFraction I f hf n ⟨(p : A[X]).coeff n, p.property n⟩, ?_⟩
  rw [map_sum]
  simp_rw [degreeZeroToFraction_homogeneousFraction]
  have he := congrArg (evaluationToChart I f) (component_sum I p)
  rw [map_sum] at he
  exact he.trans hp

end FLT.Mazur.BlowupRees

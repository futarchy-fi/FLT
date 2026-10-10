/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartPointClassification
public import FLT.Mazur.HilbertChartPointIdeal

/-!
# Classification of arbitrary prescribed-basis quotient ideals

Chart points are equivalent to all actual ambient ideals whose quotient has
the prescribed polynomial basis. Both inverse identities are proved using
the tensor reconstruction and parameter recovery.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type*) [CommRing S] [Algebra R S]

/-- Recovering the parameter from the actual fiber ideal returns the original point. -/
theorem idealClassifyingMap_idealOfPoint (f : ChartRing R I d w →ₐ[R] S) :
    idealClassifyingMap R I d w S (idealOfPoint R I d w f) = f := by
  symm
  apply point_eq_classifyingMap R I d
    (quotientBasis R I d w S (idealOfPoint R I d w f))
    (quotientGenerator I S (pointIdeal R I d w f)) w
    (quotientBasis_spec R I d w S (idealOfPoint R I d w f)) f
    (pointQuotientEquiv R I d w f).symm
  intro i
  apply (pointQuotientEquiv R I d w f).injective
  exact ((pointQuotientEquiv R I d w f).apply_symm_apply _).trans
    (pointQuotientEquiv_generator R I d w f i).symm

/-- The scalar extension at the classifying point recovers the entire original ideal. -/
theorem idealOfPoint_idealClassifyingMap (J : PrescribedBasisIdeals R I d w S) :
    idealOfPoint R I d w (idealClassifyingMap R I d w S J) = J := by
  apply Subtype.ext
  change RingHom.ker (pointEvaluation R I d w
    (classifyingMap R I d (quotientBasis R I d w S J) (quotientGenerator I S J.val) w
      (quotientBasis_spec R I d w S J))).toRingHom = J.val
  rw [pointReconstruction_ker, quotientGenerator_aeval]
  exact Ideal.Quotient.mkₐ_ker S J.val

/-- Actual chart points classify all prescribed-basis quotient ideals, including rank zero. -/
def chartClassification : (ChartRing R I d w →ₐ[R] S) ≃ PrescribedBasisIdeals R I d w S where
  toFun := idealOfPoint R I d w
  invFun := idealClassifyingMap R I d w S
  left_inv := idealClassifyingMap_idealOfPoint R I d w S
  right_inv := idealOfPoint_idealClassifyingMap R I d w S

/-- Equal actual ambient fiber ideals force equal chart parameters. -/
theorem pointIdeal_injective : Function.Injective (pointIdeal R I d w (S := S)) := by
  intro f g h
  apply (chartClassification R I d w S).injective
  exact Subtype.ext h

end FLT.Mazur.HilbertChart

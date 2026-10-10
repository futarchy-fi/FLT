/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientFactorization
public import FLT.Mazur.HilbertChartClassification

/-!
# Classification by closed ambient Hilbert charts

The actual quotient chart represents all prescribed-basis polynomial ideals
containing the original ambient equations after scalar extension. Both
inverse laws use the full ideals, without assuming a factorization witness.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R) (K : Ideal (MvPolynomial I R))

/-- Cache the coefficient ring for ambient quotient maps. -/
local instance ambientClassificationCoefficientsRing : CommRing (Coefficients R I d) :=
  inferInstance
/-- Cache the chart ring for ambient quotient maps. -/
local instance ambientClassificationChartRing : CommRing (ChartRing R I d w) := inferInstance

variable (S : Type*) [CommRing S] [Algebra R S]

/-- All actual prescribed-basis quotients satisfying the original ambient equations. -/
def AmbientPrescribedBasisIdeals :=
  { J : PrescribedBasisIdeals R I d w S //
    K.map (MvPolynomial.map (algebraMap R S)) ≤ J.val }

/-- Forget the ambient closed equations by composing with their actual quotient map. -/
def ambientChartForget (g : AmbientChartRing R I d w K →ₐ[R] S) :
    ChartRing R I d w →ₐ[R] S :=
  g.comp (Ideal.Quotient.mkₐ R (ambientRelationsIdeal R I d w K))

/-- Every point of the closed chart has its full family contained in the ambient scheme. -/
theorem ambientChartForget_contains (g : AmbientChartRing R I d w K →ₐ[R] S) :
    K.map (MvPolynomial.map (algebraMap R S)) ≤
      pointIdeal R I d w (ambientChartForget R I d w K S g) := by
  apply (ambientRelationsIdeal_le_ker_point_iff R I d w _ K).mp
  intro a ha
  change g (Ideal.Quotient.mk (ambientRelationsIdeal R I d w K) a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- The full quotient family attached to a point of the actual ambient closed chart. -/
def ambientIdealOfPoint (g : AmbientChartRing R I d w K →ₐ[R] S) :
    AmbientPrescribedBasisIdeals R I d w K S :=
  ⟨idealOfPoint R I d w (ambientChartForget R I d w K S g),
    ambientChartForget_contains R I d w K S g⟩

/-- The constructed classifying map of an arbitrary prescribed-basis ambient quotient. -/
def ambientIdealClassifyingMap (J : AmbientPrescribedBasisIdeals R I d w K S) :
    AmbientChartRing R I d w K →ₐ[R] S :=
  ambientChartLift R I d w (idealClassifyingMap R I d w S J.val) K (by
    have h := congrArg Subtype.val (idealOfPoint_idealClassifyingMap R I d w S J.val)
    change pointIdeal R I d w (idealClassifyingMap R I d w S J.val) = J.val.val at h
    rw [h]
    exact J.property)

/-- Forgetting the ambient factorization recovers the original polynomial quotient parameter. -/
theorem ambientIdealClassifyingMap_comp (J : AmbientPrescribedBasisIdeals R I d w K S) :
    ambientChartForget R I d w K S (ambientIdealClassifyingMap R I d w K S J) =
      idealClassifyingMap R I d w S J.val :=
  ambientChartLift_comp R I d w _ K _

/-- Classifying the actual closed-chart family recovers its original parameter. -/
theorem ambientIdealClassifyingMap_idealOfPoint (g : AmbientChartRing R I d w K →ₐ[R] S) :
    ambientIdealClassifyingMap R I d w K S (ambientIdealOfPoint R I d w K S g) = g := by
  apply Ideal.Quotient.algHom_ext
  change ambientChartForget R I d w K S _ = ambientChartForget R I d w K S g
  rw [ambientIdealClassifyingMap_comp]
  exact idealClassifyingMap_idealOfPoint R I d w S (ambientChartForget R I d w K S g)

/-- The actual closed-chart fiber recovers the full supplied ambient quotient ideal. -/
theorem ambientIdealOfPoint_classifyingMap (J : AmbientPrescribedBasisIdeals R I d w K S) :
    ambientIdealOfPoint R I d w K S (ambientIdealClassifyingMap R I d w K S J) = J := by
  apply Subtype.ext
  change idealOfPoint R I d w (ambientChartForget R I d w K S _) = J.val
  rw [ambientIdealClassifyingMap_comp]
  exact idealOfPoint_idealClassifyingMap R I d w S J.val

/-- Actual ambient quotient chart points classify every prescribed-basis ambient ideal. -/
def ambientChartClassification :
    (AmbientChartRing R I d w K →ₐ[R] S) ≃ AmbientPrescribedBasisIdeals R I d w K S where
  toFun := ambientIdealOfPoint R I d w K S
  invFun := ambientIdealClassifyingMap R I d w K S
  left_inv := ambientIdealClassifyingMap_idealOfPoint R I d w K S
  right_inv := ambientIdealOfPoint_classifyingMap R I d w K S

end FLT.Mazur.HilbertChart

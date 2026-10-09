/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartPointFamily
public import FLT.Mazur.HilbertChartIsomorphismInvariance
public import FLT.Mazur.HilbertChartSpecializationEvaluation

/-!
# Unique parameters for arbitrary prescribed-basis quotient algebras

Every such algebra is the actual fiber at a unique chart point, with an
isomorphism preserving all ambient generators. No reconstruction is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable {S A : Type*} [CommRing S] [CommRing A] [Algebra R S] [Algebra S A]
variable [Algebra R A] [IsScalarTower R S A]
variable (v : Module.Basis (Fin d) S A) (x : I → A)
variable (w : Fin d → MvPolynomial I R)
variable (hw : ∀ i, MvPolynomial.aeval x (w i) = v i)

/-- The actual chart-point fiber reconstructs the given quotient algebra. -/
def pointReconstruction :
    PointFiber R I d w (classifyingMap R I d v x w hw) ≃ₐ[S] A :=
  chartSpecializationEquiv R I d v x w hw

/-- Reconstruction respects the ambient generators. -/
theorem pointReconstruction_generator (i : I) :
    pointReconstruction R I d v x w hw
      (pointGenerator R I d w (classifyingMap R I d v x w hw) i) = x i := by
  change chartSpecializationEquiv R I d v x w hw
    (pointGenerator R I d w (classifyingMap R I d v x w hw) i) = _
  rw [pointGenerator, fiberGenerator, chartSpecializationEquiv_inclusion, realization_generator]

/-- Reconstruction identifies the entire ambient quotient homomorphism. -/
theorem pointReconstruction_evaluation :
    (pointReconstruction R I d v x w hw).toAlgHom.comp
      (pointEvaluation R I d w (classifyingMap R I d v x w hw)) = MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  change pointReconstruction R I d v x w hw
    (pointEvaluation R I d w (classifyingMap R I d v x w hw) (MvPolynomial.X i)) = _
  rw [pointEvaluation, MvPolynomial.aeval_X, pointReconstruction_generator, MvPolynomial.aeval_X]

/-- Reconstruction recovers the full defining ideal of the original quotient. -/
theorem pointReconstruction_ker :
    RingHom.ker (pointEvaluation R I d w (classifyingMap R I d v x w hw)).toRingHom =
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial I S →ₐ[S] A).toRingHom := by
  ext p
  change pointEvaluation R I d w (classifyingMap R I d v x w hw) p = 0 ↔
    MvPolynomial.aeval x p = 0
  have h := AlgHom.congr_fun (pointReconstruction_evaluation R I d v x w hw) p
  change pointReconstruction R I d v x w hw
    (pointEvaluation R I d w (classifyingMap R I d v x w hw) p) = MvPolynomial.aeval x p at h
  rw [← h, map_eq_zero_iff _ (pointReconstruction R I d v x w hw).injective]

/-- An ambient isomorphism from a chart fiber forces its parameter to be the classifying map. -/
theorem point_eq_classifyingMap (f : ChartRing R I d w →ₐ[R] S)
    (e : PointFiber R I d w f ≃ₐ[S] A)
    (hx : ∀ i, e (pointGenerator R I d w f i) = x i) :
    f = classifyingMap R I d v x w hw := by
  rw [← classifyingMap_point R I d w f]
  exact classifyingMap_equiv R I d (pointBasis R I d w f) v
    (pointGenerator R I d w f) x e w (pointGenerator_basis R I d w f) hw hx

include hw in
/-- Existence and uniqueness of the actual chart point for every prescribed-basis quotient. -/
theorem existsUnique_point :
    ∃! f : ChartRing R I d w →ₐ[R] S,
      ∃ e : PointFiber R I d w f ≃ₐ[S] A, ∀ i, e (pointGenerator R I d w f i) = x i := by
  refine ⟨classifyingMap R I d v x w hw, ?_, ?_⟩
  · exact ⟨pointReconstruction R I d v x w hw,
      pointReconstruction_generator R I d v x w hw⟩
  · rintro f ⟨e, he⟩
    exact point_eq_classifyingMap R I d v x w hw f e he

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartPointFamily
public import FLT.Mazur.HilbertChartQuotientBasis

/-!
# The actual ambient ideal of a chart point

The kernel of the surjective ambient evaluation has a quotient isomorphic to
the actual tensor fiber. The prescribed polynomial images form its basis.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable {S : Type*} [CommRing S] [Algebra R S]
variable (f : ChartRing R I d w →ₐ[R] S)

/-- The actual ambient ideal cut out by the scalar-extended chart family. -/
def pointIdeal : Ideal (MvPolynomial I S) := RingHom.ker (pointEvaluation R I d w f).toRingHom

/-- The quotient by the actual fiber ideal is the actual tensor fiber. -/
def pointQuotientEquiv :
    (MvPolynomial I S ⧸ pointIdeal R I d w f) ≃ₐ[S] PointFiber R I d w f :=
  Ideal.quotientKerAlgEquivOfSurjective (pointEvaluation_surjective R I d w f)

/-- The quotient isomorphism respects the ambient polynomial map. -/
theorem pointQuotientEquiv_mk (p : MvPolynomial I S) :
    pointQuotientEquiv R I d w f (Ideal.Quotient.mk (pointIdeal R I d w f) p) =
      pointEvaluation R I d w f p := rfl

/-- The actual kernel ideal belongs to the prescribed-basis chart. -/
def idealOfPoint : PrescribedBasisIdeals R I d w S := by
  refine ⟨pointIdeal R I d w f,
    (pointBasis R I d w f).map (pointQuotientEquiv R I d w f).symm.toLinearEquiv, ?_⟩
  intro i
  apply (pointQuotientEquiv R I d w f).injective
  rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, AlgEquiv.apply_symm_apply,
    pointQuotientEquiv_mk, pointEvaluation_map, pointGenerator_basis]

/-- The quotient isomorphism sends every quotient generator to the tensor-fiber generator. -/
theorem pointQuotientEquiv_generator (i : I) :
    pointQuotientEquiv R I d w f (quotientGenerator I S (pointIdeal R I d w f) i) =
      pointGenerator R I d w f i := by
  rw [quotientGenerator, pointQuotientEquiv_mk, pointEvaluation, MvPolynomial.aeval_X]

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LiftedPresentationBaseChange
public import FLT.GroupScheme.ReductionGeometricFibre

/-! # Geometric fibres of the specified lifted equations

This comparison preserves polynomial representatives. Combined with
factorization of geometric points across a nilpotent quotient, it supplies
the fibre comparison needed before applying a relative-CI flatness theorem.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Algebra.Presentation
variable {B C E Ω ι σ : Type*} [CommRing B] [CommRing C] [CommRing E] [CommRing Ω]
  [Algebra B C] [Algebra C E] [Algebra B E] [IsScalarTower B C E]
  [Algebra B Ω] [Algebra C Ω] [IsScalarTower B C Ω]
  (P : Presentation C E ι σ) (g : σ → MvPolynomial ι B)
  (hg : ∀ i, MvPolynomial.map (algebraMap B C) (g i) = P.relation i)
  (hq : Function.Surjective (algebraMap B C))

/-- The fibre of the lifted presentation equals the fibre of its specified reduction. -/
def liftedPresentationFibreEquiv :
    Ω ⊗[B] (MvPolynomial ι B ⧸ Ideal.span (Set.range g)) ≃ₐ[Ω] Ω ⊗[C] E :=
  AlgHom.reductionFibreEquiv hq (P.liftedRelationAlgHom g hg)
    (P.liftedRelationMap_surjective (algebraMap B C) g hg hq)
    (P.ker_liftedRelationMap (algebraMap B C) g hg hq)

/-- Each polynomial representative has its original presented value in the geometric fibre. -/
@[simp]
theorem liftedPresentationFibreEquiv_tmul_mk (s : Ω) (f : MvPolynomial ι B) :
    P.liftedPresentationFibreEquiv (Ω := Ω) g hg hq (s ⊗ₜ[B] Ideal.Quotient.mk _ f) =
      s ⊗ₜ[C] MvPolynomial.aeval P.val (MvPolynomial.map (algebraMap B C) f) :=
  AlgHom.reductionFibreEquiv_tmul _ _ _ _ _ _

end Algebra.Presentation

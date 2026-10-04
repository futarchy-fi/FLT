/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LiftedPresentationReduction
public import FLT.GroupScheme.SurjectiveReductionBaseChange

/-! # The actual base change of a lifted presentation

The comparison retains the original presented algebra and the images of all
polynomial representatives. It does not assert flatness of the lifted quotient.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Algebra.Presentation
variable {B C E ι σ : Type*} [CommRing B] [CommRing C] [CommRing E]
  [Algebra B C] [Algebra C E] [Algebra B E] [IsScalarTower B C E]
  (P : Presentation C E ι σ) (g : σ → MvPolynomial ι B)
  (hg : ∀ i, MvPolynomial.map (algebraMap B C) (g i) = P.relation i)

/-- The specified reduction of lifted equations as a map of base algebras. -/
def liftedRelationAlgHom : (MvPolynomial ι B ⧸ Ideal.span (Set.range g)) →ₐ[B] E where
  __ := P.liftedRelationMap (algebraMap B C) g hg
  commutes' b := by
    change MvPolynomial.aeval P.val (MvPolynomial.map (algebraMap B C) (MvPolynomial.C b)) = _
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C,
      ← IsScalarTower.algebraMap_apply B C E]

/-- The actual tensor reduction of the lifted presentation is the specified original algebra. -/
def liftedPresentationBaseChangeEquiv (hq : Function.Surjective (algebraMap B C)) :
    ((MvPolynomial ι B ⧸ Ideal.span (Set.range g)) ⊗[B] C) ≃ₐ[B] E :=
  AlgHom.reductionBaseChangeEquiv hq (P.liftedRelationAlgHom g hg)
    (P.liftedRelationMap_surjective (algebraMap B C) g hg hq)
    (P.ker_liftedRelationMap (algebraMap B C) g hg hq)

/-- The tensor comparison evaluates every representative in the original presentation. -/
@[simp]
theorem liftedPresentationBaseChangeEquiv_mk_tmul_one
    (hq : Function.Surjective (algebraMap B C)) (f : MvPolynomial ι B) :
    P.liftedPresentationBaseChangeEquiv g hg hq
      (Ideal.Quotient.mk _ f ⊗ₜ[B] (1 : C)) =
      MvPolynomial.aeval P.val (MvPolynomial.map (algebraMap B C) f) :=
  AlgHom.reductionBaseChangeEquiv_tmul_one _ _ _ _ _

/-- Original coefficient-algebra points transport to the actual tensor reduction, retaining
composites with their original coordinate maps. The coordinate rings need no B-algebra structure. -/
theorem exists_point_on_lifted_reduction (hq : Function.Surjective (algebraMap B C))
    {R A H : Type*} [CommRing R] [CommRing A] [CommRing H]
    [Algebra R B] [Algebra R E] [IsScalarTower R B E] [Algebra R A] [Algebra R H]
    (f : A →ₐ[R] H) (x : A →ₐ[R] E) (y : H →ₐ[R] E) (hy : y.comp f = x) :
    ∃ z : H →ₐ[R] ((MvPolynomial ι B ⧸ Ideal.span (Set.range g)) ⊗[B] C),
      ((P.liftedPresentationBaseChangeEquiv g hg hq).restrictScalars R).toAlgHom.comp z = y ∧
      z.comp f =
        ((P.liftedPresentationBaseChangeEquiv g hg hq).restrictScalars R).symm.toAlgHom.comp x := by
  let e := (P.liftedPresentationBaseChangeEquiv g hg hq).restrictScalars R
  refine ⟨e.symm.toAlgHom.comp y, ?_, ?_⟩
  · ext h
    exact e.apply_symm_apply (y h)
  · rw [AlgHom.comp_assoc, hy]

end Algebra.Presentation

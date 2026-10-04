/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.PrincipalBaseChangeEquiv
public import FLT.Mathlib.RingTheory.MvPolynomial.RelationBaseChange

/-! # Base change of a specified principal relation quotient -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {R S σ ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A principal localization of a relation quotient commutes with coefficient base change. -/
def principalRelationBaseChangeEquiv (g : ι → MvPolynomial σ R) (a : MvPolynomial σ R) :
    (S ⊗[R] Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range g)) a)) ≃ₐ[S]
      Localization.Away (Ideal.Quotient.mk
        (Ideal.span (Set.range fun i ↦ map (algebraMap R S) (g i)))
        (map (algebraMap R S) a)) :=
  IsLocalization.Away.baseChangeEquiv (relationBaseChangeEquiv g) _ _
    (relationBaseChangeEquiv_one_tmul_mk g a)

/-- The principal comparison preserves each original polynomial representative. -/
@[simp] theorem principalRelationBaseChangeEquiv_one_tmul_mk
    (g : ι → MvPolynomial σ R) (a q : MvPolynomial σ R) :
    principalRelationBaseChangeEquiv (S := S) g a
      (1 ⊗ₜ[R] algebraMap _ (Localization.Away
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) a))
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) q)) =
      algebraMap _ _ (Ideal.Quotient.mk
        (Ideal.span (Set.range fun i ↦ map (algebraMap R S) (g i)))
        (map (algebraMap R S) q)) := by
  simp [principalRelationBaseChangeEquiv]

end MvPolynomial

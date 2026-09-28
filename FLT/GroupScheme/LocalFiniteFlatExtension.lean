/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtension
public import Mathlib.RingTheory.Etale.Descent

/-!
# Finite-flat extensions with a specified generic field

This is the local analogue of `FiniteFlatExtension`, using `FF R K`. It retains
the specified integral maps, exactness on geometric points, faithful flatness,
and the canonical torsor comparison. In particular it applies over `ℤ_[3]`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- An integral extension `0 → A → X → Q → 0` over a base with specified generic
field, with the same exactness and torsor data as `FiniteFlatExtension`. -/
structure ModelExtension (A X Q : FF R K) where
  /-- Pullback along the prescribed kernel inclusion. -/
  inclusion : ModelHom A X
  /-- Pullback along the prescribed quotient morphism. -/
  quotient : ModelHom X Q
  /-- The composite of the inclusion and quotient is the zero group morphism. -/
  compositionZero : inclusion.toAlgHom.comp quotient.toAlgHom =
    (Algebra.ofId R A.CoordinateRing).comp (Bialgebra.counitAlgHom R Q.CoordinateRing)
  /-- The map on geometric points induced by the inclusion is injective. -/
  pointsInjective : Function.Injective (genericHom inclusion)
  /-- The quotient map on geometric points is surjective. -/
  pointsSurjective : Function.Surjective (genericHom quotient)
  /-- The kernel of the quotient on geometric points is the image of the inclusion. -/
  pointsExact : ∀ x : X.Points, genericHom quotient x = 0 ↔
    ∃ a : A.Points, genericHom inclusion a = x
  /-- The integral quotient morphism is faithfully flat. -/
  quotientFaithfullyFlat : letI := quotient.toAlgHom.toRingHom.toAlgebra
    Module.FaithfullyFlat Q.CoordinateRing X.CoordinateRing
  /-- The canonical torsor comparison `(x,a) ↦ (x,x+a)` on coordinates. -/
  torsorEquiv : letI := quotient.toAlgHom.toRingHom.toAlgebra
    X.CoordinateRing ⊗[Q.CoordinateRing] X.CoordinateRing ≃ₐ[X.CoordinateRing]
      X.CoordinateRing ⊗[R] A.CoordinateRing
  /-- The second coordinate of the torsor comparison is the specified coaction. -/
  torsorEquivSecond : letI := quotient.toAlgHom.toRingHom.toAlgebra
    ∀ b : X.CoordinateRing, torsorEquiv (1 ⊗ₜ[Q.CoordinateRing] b) =
      Algebra.TensorProduct.map (AlgHom.id R X.CoordinateRing) inclusion.toAlgHom
        (Coalgebra.comul (R := R) b)

namespace ModelExtension

variable {A X Q : FF R K} (E : ModelExtension A X Q)

/-- If the kernel is étale, the prescribed quotient is an étale morphism. -/
theorem quotient_etale [Algebra.Etale R A.CoordinateRing] :
    letI := E.quotient.toAlgHom.toRingHom.toAlgebra
    Algebra.Etale Q.CoordinateRing X.CoordinateRing := by
  let : Algebra Q.CoordinateRing X.CoordinateRing := E.quotient.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R Q.CoordinateRing X.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.quotient.toAlgHom.comp_algebraMap.symm
  let : Module.FaithfullyFlat Q.CoordinateRing X.CoordinateRing := E.quotientFaithfullyFlat
  let : Algebra.Etale X.CoordinateRing (X.CoordinateRing ⊗[Q.CoordinateRing] X.CoordinateRing) :=
    Algebra.Etale.of_equiv E.torsorEquiv.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat X.CoordinateRing

include E in
/-- Extensions of étale models are étale over their integral base. -/
theorem etale [Algebra.Etale R A.CoordinateRing] [Algebra.Etale R Q.CoordinateRing] :
    Algebra.Etale R X.CoordinateRing := by
  let : Algebra Q.CoordinateRing X.CoordinateRing := E.quotient.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R Q.CoordinateRing X.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.quotient.toAlgHom.comp_algebraMap.symm
  let := E.quotient_etale
  exact Algebra.Etale.comp R Q.CoordinateRing X.CoordinateRing

end ModelExtension

end ThreeAdicPlan

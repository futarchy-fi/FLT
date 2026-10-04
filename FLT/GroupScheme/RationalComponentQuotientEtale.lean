/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalComponentQuotient
public import FLT.GroupScheme.HopfUnramifiedAugmentation
public import Mathlib.RingTheory.Smooth.Fiber

/-! # Étaleness of the original quotient by the connected component -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.FF
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))

/-- The quotient augmentation ideal is idempotent, by faithful descent from the
actual ideal cutting out the original connected component. -/
theorem rationalComponentQuotient_augmentation_idempotent :
    IsIdempotentElem (RingHom.ker
      (Bialgebra.counitAlgHom O X.rationalComponentQuotient.CoordinateRing).toRingHom) := by
  let : Algebra X.rationalComponentQuotient.CoordinateRing X.CoordinateRing :=
    X.rationalComponentProjection.toAlgHom.toRingHom.toAlgebra
  let : Module.FaithfullyFlat X.rationalComponentQuotient.CoordinateRing X.CoordinateRing :=
    X.rationalComponentProjection_faithfullyFlat
  apply Ideal.map_injective_of_faithfullyFlat (B := X.CoordinateRing)
  rw [Ideal.map_mul]
  change HopfAlgebra.augmentationIdeal X.rationalComponentProjection *
      HopfAlgebra.augmentationIdeal X.rationalComponentProjection =
    HopfAlgebra.augmentationIdeal X.rationalComponentProjection
  rw [X.rationalComponentProjection_kernel]
  change Ideal.span {1 - X.rationalComponentIdempotent X.rationalIdentityComponentIndex} *
    Ideal.span {1 - X.rationalComponentIdempotent X.rationalIdentityComponentIndex} = _
  rw [Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun a ↦ Ideal.span {a})
    (componentIdempotent_isIdempotent (rationalSpecialIdeal p X.CoordinateRing)
      X.rationalIdentityComponentIndex).one_sub.eq

/-- The actual quotient is formally unramified over the original integral base. -/
instance rationalComponentQuotient_formallyUnramified :
    Algebra.FormallyUnramified O X.rationalComponentQuotient.CoordinateRing :=
  HopfAlgebra.formallyUnramified_of_idempotent_augmentation
    X.rationalComponentQuotient_augmentation_idempotent

/-- The actual quotient is finite étale over the original integral base. -/
instance rationalComponentQuotient_etale :
    Algebra.Etale O X.rationalComponentQuotient.CoordinateRing := by
  let : Algebra.FinitePresentation O X.rationalComponentQuotient.CoordinateRing :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat
end ThreeAdicPlan.FF

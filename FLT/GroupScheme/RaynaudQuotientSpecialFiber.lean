/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFlatQuotient

/-!
# Injectivity of contracted quotient coordinates on special fibres

A contraction in a finite flat algebra over a Dedekind domain has a
torsion-free, hence projective, module quotient. Its inclusion therefore
splits linearly and remains injective under arbitrary base change, including
the nonflat base change to a residue field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.IntegralClosure

variable (R K H : Type) [CommRing R] [Field K] [Algebra R K]
    [CommRing H] [Algebra R H] [IsFractionRing R K]
    [IsDedekindDomain R] [Module.Finite R H] [Module.Flat R H]

/-- The inclusion of a contracted subalgebra remains injective after tensoring
with any module, even one that is not flat over the base. -/
theorem contraction_lTensor_injective (C : Subalgebra K (K ⊗[R] H))
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective ((contraction R K H C).val.toLinearMap.lTensor M) := by
  let D := contraction R K H C
  let : Module.IsTorsionFree R (Ideal.ModuleQuotient D.toSubmodule) :=
    contraction_quotient_isTorsionFree R K H C
  let : Module.FinitePresentation R H := Module.finitePresentation_of_finite R H
  let : Module.FinitePresentation R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.finitePresentation_of_finite R _
  let : Module.Projective R H := Module.Flat.projective_of_finitePresentation
  let : Module.Projective R (Ideal.ModuleQuotient D.toSubmodule) :=
    Module.Flat.projective_of_finitePresentation
  apply Function.LeftInverse.injective
    (g := (retraction R K H C).lTensor M)
  intro x
  change ((retraction R K H C).lTensor M).comp (D.val.toLinearMap.lTensor M) x = x
  rw [← LinearMap.lTensor_comp, retraction_comp_val, LinearMap.lTensor_id]
  rfl

end HopfAlgebra.IntegralClosure

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    {X Y : FF R K}

/-- A contracted generic quotient is still an inclusion on every base fibre.
In particular, its special fibre is a subalgebra of the source special fibre. -/
theorem GenericGaloisHom.quotientInclusion_lTensor_injective
    (q : GenericGaloisHom X Y) (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective (q.quotientInclusion.toLinearMap.lTensor M) :=
  HopfAlgebra.IntegralClosure.contraction_lTensor_injective R K X.CoordinateRing
    q.toBialgHom.toAlgHom.range M

end ThreeAdicPlan

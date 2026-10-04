/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalComponentQuotient
public import FLT.GroupScheme.GenericSurjectiveDescent

/-! # The original generic maps induced on the component quotients -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ModelHom
variable {p : ℕ} [Fact p.Prime]
variable {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)}

/-- The original morphism preserves the kernel of the actual component projection. -/
theorem rationalComponentGenericMap_ker (f : ModelHom X Y) :
    X.rationalComponentGenericProjection.toAddMonoidHom.ker ≤
      (Y.rationalComponentGenericProjection.comp (genericHom f)).toAddMonoidHom.ker := by
  intro x hx
  obtain ⟨a, rfl⟩ := (X.rationalComponentGenericProjection_exact x).mp hx
  apply (Y.rationalComponentGenericProjection_exact _).mpr
  refine ⟨genericHom f.rationalIdentityMap a, ?_⟩
  change genericHom Y.rationalIdentityComponentInclusion (genericHom f.rationalIdentityMap a) =
    genericHom f (genericHom X.rationalIdentityComponentInclusion a)
  have h := congrArg (fun k ↦ genericHom k a) f.rationalIdentityMap_naturality
  simpa only [genericHom_comp] using h

/-- The induced generic morphism is obtained by descent through the original projection. -/
def rationalComponentGenericMap (f : ModelHom X Y) :
    GenericGaloisHom X.rationalComponentQuotientWitness Y.rationalComponentQuotientWitness :=
  X.rationalComponentGenericProjection.descendThroughSurjective
    X.rationalComponentGenericProjection_surjective
    (Y.rationalComponentGenericProjection.comp (genericHom f)) f.rationalComponentGenericMap_ker

/-- The actual quotient diagram commutes on original geometric points. -/
theorem rationalComponentGenericMap_naturality (f : ModelHom X Y) :
    Y.rationalComponentGenericProjection.comp (genericHom f) =
      f.rationalComponentGenericMap.comp X.rationalComponentGenericProjection := by
  ext x
  exact (X.rationalComponentGenericProjection.descendThroughSurjective_apply
    X.rationalComponentGenericProjection_surjective _ f.rationalComponentGenericMap_ker x).symm
end ThreeAdicPlan.ModelHom

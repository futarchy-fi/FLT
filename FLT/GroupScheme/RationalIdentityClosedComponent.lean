/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityComponentMaps
public import FLT.GroupScheme.LocalIdempotentImage

/-! # Closed immersions pull back the original identity component -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ModelHom
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)}

/-- A closed immersion pulls the ambient identity idempotent back to the subgroup's one. -/
theorem rationalIdentityIdempotent_of_surjective (f : ModelHom X Y)
    (hf : Function.Surjective f) :
    f (Y.rationalComponentIdempotent Y.rationalIdentityComponentIndex) =
      X.rationalComponentIdempotent X.rationalIdentityComponentIndex := by
  apply map_local_component_idempotent (e := Y.rationalComponentIdempotent
    Y.rationalIdentityComponentIndex) (d := X.rationalComponentIdempotent
    X.rationalIdentityComponentIndex) f.toAlgHom.toRingHom hf
    (Bialgebra.counitAlgHom O X.CoordinateRing).toRingHom
    (componentIdempotent_isIdempotent _ _) (componentIdempotent_isIdempotent _ _)
  · exact (CoalgHomClass.counit_comp_apply f _).trans
      Y.counit_rationalIdentityComponentIdempotent
  · exact X.counit_rationalIdentityComponentIdempotent
  · exact f.rationalIdentity_idempotent

/-- The ideal cutting out the identity component pulls back under a closed immersion. -/
theorem rationalIdentityIdeal_map_of_surjective (f : ModelHom X Y)
    (hf : Function.Surjective f) :
    Y.rationalIdentityComponentIdeal.map f.toAlgHom.toRingHom =
      X.rationalIdentityComponentIdeal := by
  change (Ideal.span {1 - Y.rationalComponentIdempotent Y.rationalIdentityComponentIndex}).map
    f.toAlgHom.toRingHom = Ideal.span {1 - (X.rationalComponentIdempotent
      X.rationalIdentityComponentIndex)}
  rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  exact congrArg (fun a ↦ Ideal.span {1 - a})
    (f.rationalIdentityIdempotent_of_surjective hf)
end ThreeAdicPlan.ModelHom

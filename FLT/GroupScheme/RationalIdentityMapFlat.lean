/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityComponentMaps
public import FLT.GroupScheme.FlatSurjectiveBase

/-! # Flatness of the original map restricted to the identity components -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ModelHom
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
variable {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)}

/-- Restricting a flat original morphism to identity components preserves flatness. -/
theorem rationalIdentityMap_flat (f : ModelHom X Y) (hf : f.toAlgHom.toRingHom.Flat) :
    f.rationalIdentityMap.toAlgHom.toRingHom.Flat := by
  let : Algebra Y.CoordinateRing X.CoordinateRing := f.toAlgHom.toRingHom.toAlgebra
  let : Module.Flat Y.CoordinateRing X.CoordinateRing := hf
  have hflat : Module.Flat Y.CoordinateRing
      (X.RationalComponentAlgebra X.rationalIdentityComponentIndex) :=
    flat_quotient_complement_idempotent
      (componentIdempotent_isIdempotent (rationalSpecialIdeal p X.CoordinateRing) _)
  apply RingHom.Flat.of_comp_surjective
    Y.rationalIdentityComponentProjection.toRingHom _ Ideal.Quotient.mk_surjective
  have hsquare : f.rationalIdentityMap.toAlgHom.toRingHom.comp
      Y.rationalIdentityComponentProjection.toRingHom =
      X.rationalIdentityComponentProjection.toRingHom.comp f.toAlgHom.toRingHom := by
    ext a
    rfl
  rw [hsquare]
  exact hflat
end ThreeAdicPlan.ModelHom

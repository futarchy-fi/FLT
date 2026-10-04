/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityMapFlat
public import FLT.GroupScheme.RationalConnectedLevelTower

/-! # Faithful flatness of the original connected reductions -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- The counit from the local identity-component algebra reflects units. -/
theorem FF.rationalIdentityComponentCounit_isLocalHom (X : FF
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) :
    IsLocalHom X.rationalIdentityComponentCounit.toRingHom :=
  IsLocalHom.of_surjective _ (fun a ↦ ⟨algebraMap O _ a,
    X.rationalIdentityComponentCounit.commutes a⟩)

/-- The restricted coordinate map is a local map, as witnessed by its original counit. -/
theorem ModelHom.rationalIdentityMap_isLocalHom {X Y : FF
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} (f : ModelHom X Y) :
    IsLocalHom f.rationalIdentityMap.toAlgHom.toRingHom := by
  let := Y.rationalIdentityComponentCounit_isLocalHom
  constructor
  intro a ha
  apply isUnit_of_map_unit Y.rationalIdentityComponentCounit.toRingHom a
  have h := ha.map X.rationalIdentityComponentCounit.toRingHom
  convert h using 1
  exact (CoalgHomClass.counit_comp_apply f.rationalIdentityMap a).symm

/-- Any flat original group morphism restricts to a faithfully flat connected morphism. -/
theorem ModelHom.rationalIdentityMap_faithfullyFlat {X Y : FF
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)} (f : ModelHom X Y)
    (hf : f.toAlgHom.toRingHom.Flat) :
    f.rationalIdentityMap.toAlgHom.toRingHom.FaithfullyFlat := by
  let : Algebra Y.rationalIdentityComponent.CoordinateRing
      X.rationalIdentityComponent.CoordinateRing :=
    f.rationalIdentityMap.toAlgHom.toRingHom.toAlgebra
  let : Module.Flat Y.rationalIdentityComponent.CoordinateRing
      X.rationalIdentityComponent.CoordinateRing := f.rationalIdentityMap_flat hf
  let := f.rationalIdentityMap_isLocalHom
  let : IsLocalRing Y.rationalIdentityComponent.CoordinateRing :=
    Y.rationalComponentAlgebra_isLocalRing _
  let : IsLocalRing X.rationalIdentityComponent.CoordinateRing :=
    X.rationalComponentAlgebra_isLocalRing _
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The actual connected reductions are faithfully flat, with no extra system hypothesis. -/
theorem PDivisibleSystem.rationalConnectedReduction_faithfullyFlat {height : ℕ}
    (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height)
    {m n : ℕ} (h : m ≤ n) :
    (X.rationalConnectedReduction h).toAlgHom.toRingHom.FaithfullyFlat :=
  (X.reduction h).rationalIdentityMap_faithfullyFlat (X.faithfullyFlat h).flat
end ThreeAdicPlan

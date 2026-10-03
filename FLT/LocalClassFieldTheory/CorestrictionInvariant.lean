/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RestrictionSurjective
public import FLT.LocalClassFieldTheory.AbsoluteCorestriction

/-!
# Corestriction preserves the local invariant

Restriction is surjective, and the constructed coset-sum corestriction composed
with it is degree multiplication. The restriction invariant formula therefore
proves compatibility of corestriction with the actual local invariant.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S K C : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  (E : IntermediateField K C)
  [Algebra S E] [IsFractionRing S E] [Algebra S C] [IsScalarTower S E C]
  [IsScalarTower R S C] [IsScalarTower R S E]
  [Algebra.IsSeparable K C] [IsSepClosed C]
  [Finite (ResidueField R)] [Finite (ResidueField S)]
  [IsAdicComplete (maximalIdeal R) R] [IsAdicComplete (maximalIdeal S) S]

local notation "A" => maximalUnramified R K C
local notation "B" => maximalUnramified S E C

attribute [local instance] unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

attribute [local instance] relativeBaseTower

variable [FiniteDimensional K E] [CharZero C]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p] [CharP (ResidueField S) p]

/-- Actual continuous corestriction preserves the normalized absolute invariant. -/
theorem absoluteInvariant_corestriction
    (y : continuousCohomology ℤ Gal(C/E) (Additive Cˣ) 2) :
    absoluteInvariant R K C p (absoluteCorestriction K C E y) =
      absoluteInvariant S E C p y := by
  obtain ⟨x, rfl⟩ := absoluteRestrictionH2_surjective R S K C E p y
  rw [absoluteCorestriction_restriction, map_nsmul,
    absoluteInvariant_restriction R S K C E p]

include R S p in
/-- The constructed absolute H2 corestriction is bijective. -/
theorem absoluteCorestriction_bijective :
    Function.Bijective (absoluteCorestriction K C E) := by
  have he : (absoluteCorestriction K C E :
      continuousCohomology ℤ Gal(C/E) (Additive Cˣ) 2 →
        continuousCohomology ℤ Gal(C/K) (Additive Cˣ) 2) =
      (absoluteInvariant R K C p).symm ∘ absoluteInvariant S E C p := by
    funext y
    apply (absoluteInvariant R K C p).injective
    rw [absoluteInvariant_corestriction R S K C E p]
    simp
  rw [he]
  exact (absoluteInvariant R K C p).symm.bijective.comp
    (absoluteInvariant S E C p).bijective

end LocalClassFieldTheory

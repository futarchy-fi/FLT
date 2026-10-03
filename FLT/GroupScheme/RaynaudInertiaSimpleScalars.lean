/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudAbsoluteTameCommutativity
public import FLT.GroupScheme.RaynaudTameQuotientScalars
public import FLT.AbsoluteGaloisGroup.WildInertiaProP

/-!
# Derived scalar fields for simple local inertia representations

The continuous finite image of wild inertia is a p-group. It fixes an
irreducible representation, whose remaining action factors through the
proved commutative tame quotient. This derives a scalar field of rank one.
-/

@[expose] public noncomputable section
namespace LocalRamification
open NumberField IsLocalRing

universe u
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  {V : Type u} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  (ρ : Representation (ZMod p) (localInertiaGroup v) V) [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) V)ˣ]
  [DiscreteTopology (Module.End (ZMod p) V)ˣ]

/-- Every continuous simple finite local inertia representation has derived rank-one scalars. -/
theorem exists_rank_one_scalar_field_of_local_inertia (hρ : Continuous ρ.toHomUnits) :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F V),
      Module.finrank F V = 1 ∧ ∀ (a : F) (g : localInertiaGroup v) (x : V),
        ρ g (a • x) = a • ρ g x := by
  let : Finite (Module.End (ZMod p) V) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  apply ρ.exists_rank_one_scalar_field_of_tame_quotient (wildInertia v) _
    (tameInertia_commute v)
  exact wildInertia_finite_image_isPGroup v p _ (ρ.toHomUnits.comp (wildInertia v).subtype)
    (hρ.comp continuous_subtype_val)

end LocalRamification

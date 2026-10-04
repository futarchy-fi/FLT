/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.SerreWeight.NormalizedCharacterExponent
public import FLT.GaloisRepresentation.SerreWeight.OrdinaryBranch

/-!
# Normalized recipe inputs extracted from ordinary representations

Over prime-field coefficients, a surjective inertia character and the
kernel containment extract the normalized exponent. The whole-local
cyclotomic non-peu branch then has exponent one by proof. This constructs
the existing recipe input without accepting a branch label or weight.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.SerreWeight

/-- A surjective prime-field unit character has normalized exponent one relative to itself. -/
theorem normalizedCharacterExponent_self {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (θ : G →* (ZMod p)ˣ) (hθ : Function.Surjective θ) :
    normalizedCharacterExponent θ θ hθ le_rfl = 1 := by
  obtain ⟨hb, hb', he⟩ := normalizedCharacterExponent_spec θ θ hθ le_rfl
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  obtain ⟨g, hg⟩ := hθ u
  have hp : u ^ (normalizedCharacterExponent θ θ hθ le_rfl - 1) = 1 := by
    apply mul_right_cancel (b := u)
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel hb, ← hg, ← he]
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hu, Nat.card_eq_fintype_card, ZMod.card_units] at hd
  have hz := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

end GaloisRepresentation.SerreWeight

namespace GaloisRepresentation.Extensions.OrdinaryFiltration
open SerreWeight SerreWeightRecipe

variable {G V : Type*} [Group G] {p : ℕ} [Fact p.Prime]
  [AddCommGroup V] [Module (ZMod p) V]
  [TopologicalSpace G] [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]
  [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation (ZMod p) G V} {α β : G →* (ZMod p)ˣ}
  (E : OrdinaryFiltration ρ α β)
  (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))
  (I : Subgroup G) (ε : G →* (ZMod p)ˣ)
  (hε : Function.Surjective (ε.comp I.subtype))
  (hker : (ε.comp I.subtype).ker ≤ ((homCharacter α β).comp I.subtype).ker)

/-- All fields of the normalized recipe input are extracted from the actual filtration. -/
def normalizedOrdinaryInput : ReducibleInput p where
  exponent := normalizedCharacterExponent (ε.comp I.subtype)
    ((homCharacter α β).comp I.subtype) hε hker
  lower := (normalizedCharacterExponent_spec _ _ hε hker).1
  upper := (normalizedCharacterExponent_spec _ _ hε hker).2.1
  extensionCase := E.ordinaryBranch hρ I ε
  exceptionalExponent := by
    intro ht
    have he := ((E.ordinaryBranch_tres_iff hρ I ε).mp ht).1
    subst ε
    exact normalizedCharacterExponent_self _ hε

/-- The extracted exponent recovers the actual Hom character on every inertia element. -/
theorem normalizedOrdinaryInput_character (g : I) :
    homCharacter α β g = ε g ^ (E.normalizedOrdinaryInput hρ I ε hε hker).exponent :=
  (normalizedCharacterExponent_spec _ _ hε hker).2.2 g

end GaloisRepresentation.Extensions.OrdinaryFiltration

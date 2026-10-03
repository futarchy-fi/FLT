/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.CharacterCoefficients

/-!
# Actual Hom coefficients for ordinary character lines

The action is the existing Hom representation. Evaluation at 1 identifies
it with a scalar-extended character when the Hom character has that value.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {G F k : Type*} [Group G] [Field F] [Field k] [Algebra F k]

/-- The Hom space of two character lines, with its representation action. -/
def OrdinaryHomModule (_α _β : G →* kˣ) := k →ₗ[k] k

variable (α β : G →* kˣ)

instance : AddCommGroup (OrdinaryHomModule α β) := inferInstanceAs (AddCommGroup (k →ₗ[k] k))
instance : Module k (OrdinaryHomModule α β) := inferInstanceAs (Module k (k →ₗ[k] k))
instance : TopologicalSpace (OrdinaryHomModule α β) := ⊥
instance : DiscreteTopology (OrdinaryHomModule α β) := ⟨rfl⟩

instance : DistribMulAction G (OrdinaryHomModule α β) where
  smul g f := Representation.linHom (characterLine β) (characterLine α) g f
  one_smul f := by
    change Representation.linHom (characterLine β) (characterLine α) 1 f = f
    rw [map_one]
    rfl
  mul_smul g h f := by
    change Representation.linHom (characterLine β) (characterLine α) (g * h) f = _
    rw [map_mul]
    rfl
  smul_zero g := map_zero _
  smul_add g f h := map_add _ _ _

instance : SMulCommClass G k (OrdinaryHomModule α β) where
  smul_comm g a f := (Representation.linHom (characterLine β) (characterLine α) g).map_smul a f

variable (χ : G →* Fˣ)
    (hχ : homCharacter α β = (Units.map (algebraMap F k).toMonoidHom).comp χ)

/-- Evaluation at 1 gives the actual linear coordinate map of the Hom space. -/
def ordinaryHomCoordinates : OrdinaryHomModule α β ≃ₗ[k] CharacterModule χ k :=
  characterHomCoordinates

include hχ in
/-- The actual Hom action becomes the scalar-extended character action. -/
theorem ordinaryHomCoordinates_equivariant (g : G) (f : OrdinaryHomModule α β) :
    ordinaryHomCoordinates α β χ (g • f) = g • ordinaryHomCoordinates α β χ f := by
  dsimp [OrdinaryHomModule] at f
  change (Representation.linHom (characterLine β) (characterLine α) g f) 1 =
    algebraMap F k (χ g : F) * f 1
  rw [characterLine_linHom_apply, hχ]
  rfl

include hχ in
/-- The same constructed coordinates remain equivariant after any simultaneous twist. -/
theorem ordinaryHomCoordinates_twist_equivariant (ψ : G →* kˣ) (g : G)
    (f : OrdinaryHomModule (α * ψ) (β * ψ)) :
    ordinaryHomCoordinates (α * ψ) (β * ψ) χ (g • f) =
      g • ordinaryHomCoordinates (α * ψ) (β * ψ) χ f :=
  ordinaryHomCoordinates_equivariant (α * ψ) (β * ψ) χ (by rw [homCharacter_twist, hχ]) g f

/-- A simultaneous twist uses the identity on the underlying Hom coefficient group. -/
def ordinaryHomTwistEquiv (ψ : G →* kˣ) :
    OrdinaryHomModule α β ≃+ OrdinaryHomModule (α * ψ) (β * ψ) := AddEquiv.refl _

/-- That identity intertwines the actual twisted Hom representation. -/
theorem ordinaryHomTwistEquiv_equivariant (ψ : G →* kˣ) (g : G)
    (f : OrdinaryHomModule α β) :
    ordinaryHomTwistEquiv α β ψ (g • f) = g • ordinaryHomTwistEquiv α β ψ f := by
  change Representation.linHom (characterLine β) (characterLine α) g f =
    Representation.linHom (characterLine (β * ψ)) (characterLine (α * ψ)) g f
  rw [characterLine_linHom_twist]

end GaloisRepresentation.Extensions

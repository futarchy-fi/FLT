/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Ring

/-!
# Character lines and their Hom coefficients

For an extension of the beta line by the alpha line, the coefficient
character is alpha / beta. A simultaneous twist cancels in this character.
Unramified means trivial on the specified inertia subgroup.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {k G : Type*} [Field k] [Group G]

/-- The one-dimensional representation associated to a unit-valued character. -/
def characterLine (χ : G →* kˣ) : Representation k G k where
  toFun g := (χ g : k) • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' g h := by apply LinearMap.ext; intro x; simp [mul_assoc, mul_left_comm]

/-- The coefficient character of maps from the beta line to the alpha line. -/
def homCharacter (α β : G →* kˣ) : G →* kˣ := α / β

/-- Evaluation identifies the Hom action with multiplication by the quotient character. -/
theorem characterLine_linHom_apply (α β : G →* kˣ) (g : G) (f : k →ₗ[k] k) (x : k) :
    (Representation.linHom (characterLine β) (characterLine α) g f) x =
      (homCharacter α β g : k) * f x := by
  simp only [Representation.linHom_apply, characterLine, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, homCharacter, MonoidHom.div_apply, Units.val_div_eq_div_val,
    map_inv, Units.val_inv_eq_inv_val]
  rw [show f ((↑(β g) : k)⁻¹ * x) = (↑(β g) : k)⁻¹ * f x from
    f.map_smul (↑(β g) : k)⁻¹ x]
  ring

/-- Coordinates identify the Hom space of two lines with the scalar field. -/
def characterHomCoordinates : (k →ₗ[k] k) ≃ₗ[k] k := LinearMap.ringLmapEquivSelf k k k

/-- The coordinate equivalence intertwines the Hom representation and quotient character. -/
theorem characterHomCoordinates_equivariant (α β : G →* kˣ) (g : G) (f : k →ₗ[k] k) :
    characterHomCoordinates (Representation.linHom (characterLine β) (characterLine α) g f) =
      characterLine (homCharacter α β) g (characterHomCoordinates f) :=
  characterLine_linHom_apply α β g f 1

/-- A simultaneous character twist leaves the Hom coefficient character unchanged. -/
theorem homCharacter_twist (α β χ : G →* kˣ) :
    homCharacter (α * χ) (β * χ) = homCharacter α β := by
  ext g
  simp [homCharacter]

/-- A character is unramified relative to an inertia subgroup if it is trivial there. -/
def CharacterUnramified (I : Subgroup G) (χ : G →* kˣ) : Prop :=
  ∀ g ∈ I, χ g = 1

/-- An unramified twist preserves a character on inertia. -/
theorem unramified_twist_on_inertia (I : Subgroup G) (α χ : G →* kˣ)
    (hχ : CharacterUnramified I χ) (g : G) (hg : g ∈ I) :
    (α * χ) g = α g := by
  simp [hχ g hg]

/-- The identity on the Hom space intertwines a simultaneous twist. -/
theorem characterLine_linHom_twist (α β χ : G →* kˣ) :
    Representation.linHom (characterLine (β * χ)) (characterLine (α * χ)) =
      Representation.linHom (characterLine β) (characterLine α) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  simp only [characterLine_linHom_apply, homCharacter_twist]

/-- The coordinates of a linear map between lines after rescaling their bases.
The sub-line basis is multiplied by a, the quotient-line basis by b. -/
theorem line_basis_factor (a b : kˣ) (f : k →ₗ[k] k) :
    (a : k)⁻¹ * f (b : k) = ((b / a : kˣ) : k) * f 1 := by
  have hf : f (b : k) = (b : k) * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul (b : k) (1 : k)
  rw [hf, Units.val_div_eq_div_val]
  ring

end GaloisRepresentation.Extensions

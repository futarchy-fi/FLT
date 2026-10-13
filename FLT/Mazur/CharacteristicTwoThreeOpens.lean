/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Tactic.Ring

/-!
# Characteristic opens on every original base scheme

The opens where two and three are invertible cover an arbitrary scheme. Their
global sections have the required unit, including on nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CharacteristicTwoThree
variable (S : Scheme)

/-- The original base open on which the chosen integer is invertible. -/
def unitOpen (n : ℕ) : S.Opens := S.basicOpen (n : Γ(S, ⊤))

/-- The integer is a unit in the global functions of its actual open subscheme. -/
theorem unitOpen_isUnit (n : ℕ) : IsUnit (n : Γ((unitOpen S n).toScheme, ⊤)) := by
  apply (unitOpen S n).toScheme.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  apply ((unitOpen S n).toScheme.mem_basicOpen_top _ x).mp
  have h : x ∈ (unitOpen S n).ι ⁻¹ᵁ S.basicOpen (n : Γ(S, ⊤)) := x.2
  simpa only [Scheme.preimage_basicOpen_top, map_natCast] using h

/-- At every original point, either two or three is invertible. -/
theorem mem_two_or_three (x : S) : x ∈ unitOpen S 2 ∨ x ∈ unitOpen S 3 := by
  have hu : IsUnit (-(2 : S.presheaf.stalk x) + 3) := by
    convert isUnit_one (M := S.presheaf.stalk x) using 1
    ring
  have h := IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu
  have h' : IsUnit (2 : S.presheaf.stalk x) ∨ IsUnit (3 : S.presheaf.stalk x) :=
    h.imp (fun h₂ ↦ by simpa only [neg_neg] using h₂.neg) id
  simpa only [unitOpen, Scheme.mem_basicOpen_top, map_natCast, Nat.cast_ofNat, map_ofNat]
    using h'

/-- The actual two characteristic opens cover the original base. -/
theorem two_sup_three : unitOpen S 2 ⊔ unitOpen S 3 = ⊤ := by
  apply top_unique
  intro x _
  exact mem_two_or_three S x

end FLT.Mazur.CharacteristicTwoThree

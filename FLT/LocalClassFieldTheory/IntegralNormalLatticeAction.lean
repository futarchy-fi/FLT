/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralNormalLattice
public import Mathlib.RepresentationTheory.Coinduced

/-!
# The integral normal lattice as a coinduced module

Inverse-indexed normal-basis coordinates turn the actual Galois action
into the right translation action used by coinduction from the trivial subgroup.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

set_option backward.isDefEq.respectTransparency false

variable (R K L : Type) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L/K)
local notation "V" => integralNormalLattice R K L
local notation "b" => integralNormalLatticeBasis R K L

/-- The actual Galois representation on the constructed integral normal lattice. -/
def integralNormalLatticeRepresentation : Representation R G V where
  toFun g := ((g.restrictScalars R).toLinearMap.domRestrict V).codRestrict V
    (fun x => integralNormalLattice_action_mem R K L g x x.property)
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

/-- The representation permutes the lattice basis by left multiplication. -/
theorem integralNormalLatticeRepresentation_basis (g h : G) :
    integralNormalLatticeRepresentation R K L g (b h) = b (g * h) := by
  apply Subtype.ext
  change g (b h : L) = (b (g * h) : L)
  simp only [integralNormalLatticeBasis_val]
  exact integralNormalBasis_action R K L g h

/-- The underlying lattice is equivalent to functions on the Galois group. -/
def integralNormalLatticeCoordinates : V ≃ₗ[R] (G → R) :=
  (b).equivFun

/-- Coordinates of the Galois action are left translation of the argument. -/
theorem integralNormalLatticeCoordinates_action (g : G) (x : V) (h : G) :
    integralNormalLatticeCoordinates R K L
      (integralNormalLatticeRepresentation R K L g x) h =
      integralNormalLatticeCoordinates R K L x (g⁻¹ * h) := by
  classical
  have he : (integralNormalLatticeCoordinates R K L).toLinearMap.comp
      (integralNormalLatticeRepresentation R K L g) =
      (LinearMap.funLeft R R (fun h : G => g⁻¹ * h)).comp
        (integralNormalLatticeCoordinates R K L).toLinearMap := by
    apply (b).ext
    intro j
    ext h
    simp [integralNormalLatticeRepresentation_basis, integralNormalLatticeCoordinates,
      Module.Basis.equivFun_apply, Finsupp.single_apply, eq_inv_mul_iff_mul_eq]
  exact congrArg (fun z : G → R => z h) (LinearMap.congr_fun he x)

/-- Inverse-indexed coordinates lie in coinduction from the trivial subgroup. -/
def integralNormalLatticeCoindMap : V →ₗ[R]
    Representation.coindV (⊥ : Subgroup G).subtype (Representation.trivial R (⊥ : Subgroup G) R) :=
  ((LinearMap.funLeft R R (fun g : G => g⁻¹)).comp
    (integralNormalLatticeCoordinates R K L).toLinearMap).codRestrict _ fun x g h => by
      have hg : (g : G) = 1 := g.property
      simp [hg, Representation.trivial]

/-- Coinduction coordinates retain every lattice element and every function. -/
theorem integralNormalLatticeCoindMap_bijective :
    Function.Bijective (integralNormalLatticeCoindMap R K L) := by
  constructor
  · intro x y h
    apply (integralNormalLatticeCoordinates R K L).injective
    funext g
    have he := congrArg (fun z => z.val g⁻¹) h
    change integralNormalLatticeCoordinates R K L x (g⁻¹)⁻¹ =
      integralNormalLatticeCoordinates R K L y (g⁻¹)⁻¹ at he
    simpa only [inv_inv] using he
  · intro f
    refine ⟨(integralNormalLatticeCoordinates R K L).symm (fun g => f.val g⁻¹), ?_⟩
    apply Subtype.ext
    funext g
    change integralNormalLatticeCoordinates R K L
      ((integralNormalLatticeCoordinates R K L).symm _) g⁻¹ = _
    simp

/-- The normal lattice is linearly equivalent to the actual coinduced module. -/
def integralNormalLatticeCoindEquiv : V ≃ₗ[R]
    Representation.coindV (⊥ : Subgroup G).subtype (Representation.trivial R (⊥ : Subgroup G) R) :=
  LinearEquiv.ofBijective (integralNormalLatticeCoindMap R K L)
    (integralNormalLatticeCoindMap_bijective R K L)

/-- The equivalence intertwines the actual Galois and coinduced actions. -/
theorem integralNormalLatticeCoindEquiv_action (g : G) (x : V) :
    integralNormalLatticeCoindEquiv R K L (integralNormalLatticeRepresentation R K L g x) =
      Representation.coind (⊥ : Subgroup G).subtype
        (Representation.trivial R (⊥ : Subgroup G) R) g
          (integralNormalLatticeCoindEquiv R K L x) := by
  apply Subtype.ext
  funext h
  change integralNormalLatticeCoordinates R K L
    (integralNormalLatticeRepresentation R K L g x) h⁻¹ =
      integralNormalLatticeCoordinates R K L x (h * g)⁻¹
  rw [integralNormalLatticeCoordinates_action, mul_inv_rev]

end LocalClassFieldTheory

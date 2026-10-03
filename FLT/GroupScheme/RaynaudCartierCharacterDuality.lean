/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudAugmentationDuality
public import FLT.GroupScheme.RaynaudCharacterDuality

/-!
# The actual Cartier pairing on character summands

The transposed integral scalar maps satisfy the scalar-unit action laws.
The actual augmentation pairing intertwines that action with transposition,
so its restriction is a perfect pairing on each character summand.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open CharacterProjector

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K] [Field F]
  (X : FF R K) (lift : F → ModelHom X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))

include h1 in
/-- Dualizing the unit scalar gives the identity on the actual dual model. -/
theorem FF.dualScalar_one : (lift 1).cartierDual = BialgHom.id R X.cartierDual.CoordinateRing := by
  rw [h1]
  ext φ
  rfl

include hmul in
/-- The integral dual scalar maps obey the contravariant scalar multiplication law. -/
theorem FF.dualScalar_mul (a b : F) :
    (lift (a * b)).cartierDual = (lift b).cartierDual.comp (lift a).cartierDual := by
  rw [mul_comm a b, hmul]
  ext φ
  rfl

/-- The scalar-unit representation on the actual dual augmentation ideal. -/
def FF.dualAugmentationRepresentation : Representation R Fˣ X.cartierDual.augmentation :=
  X.cartierDual.augmentationRepresentation (fun a ↦ (lift a).cartierDual)
    (X.dualScalar_one lift h1) (X.dualScalar_mul lift hmul)

/-- The actual augmentation pairing intertwines dual scalars with transposition. -/
theorem FF.augmentationDuality_intertwines (g : Fˣ) (φ : X.cartierDual.augmentation) :
    X.augmentationDuality (X.dualAugmentationRepresentation lift h1 hmul g φ) =
      transpose (X.augmentationRepresentation lift h1 hmul) g (X.augmentationDuality φ) := by
  ext a
  rfl

/-- Restrict the actual pairing equivalence to matching character eigenspaces. -/
def FF.cartierCharacterTranspose (χ : Fˣ →* Rˣ) :
    eigenspace (X.dualAugmentationRepresentation lift h1 hmul) χ ≃ₗ[R]
      eigenspace (transpose (X.augmentationRepresentation lift h1 hmul)) χ where
  toFun φ := ⟨X.augmentationDuality φ.val, by
    apply (mem_eigenspace_iff _ _ _).mpr
    intro g
    rw [← X.augmentationDuality_intertwines]
    rw [(mem_eigenspace_iff _ _ _).mp φ.property g, map_smul]⟩
  invFun ψ := ⟨X.augmentationDuality.symm ψ.val, by
    apply (mem_eigenspace_iff _ _ _).mpr
    intro g
    apply X.augmentationDuality.injective
    rw [X.augmentationDuality_intertwines, LinearEquiv.apply_symm_apply,
      map_smul, LinearEquiv.apply_symm_apply]
    exact (mem_eigenspace_iff _ _ _).mp ψ.property g⟩
  left_inv φ := by apply Subtype.ext; exact X.augmentationDuality.symm_apply_apply φ.val
  right_inv ψ := by apply Subtype.ext; exact X.augmentationDuality.apply_symm_apply ψ.val
  map_add' φ ψ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r φ := by apply Subtype.ext; exact map_smul _ _ _

variable [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)]

/-- The Cartier dual character summand is the full dual of the original summand. -/
def FF.cartierCharacterDuality (χ : Fˣ →* Rˣ) :
    eigenspace (X.dualAugmentationRepresentation lift h1 hmul) χ ≃ₗ[R]
      Module.Dual R (eigenspace (X.augmentationRepresentation lift h1 hmul) χ) :=
  (X.cartierCharacterTranspose lift h1 hmul χ).trans
    (duality (X.augmentationRepresentation lift h1 hmul) χ)

/-- The perfect character pairing is evaluation of the actual dual coordinate. -/
@[simp] theorem FF.cartierCharacterDuality_apply (χ : Fˣ →* Rˣ)
    (φ : eigenspace (X.dualAugmentationRepresentation lift h1 hmul) χ)
    (a : eigenspace (X.augmentationRepresentation lift h1 hmul) χ) :
    X.cartierCharacterDuality lift h1 hmul χ φ a =
      (show HopfAlgebra.CartierDual R X.CoordinateRing from φ.val.val) a.val := rfl

end ThreeAdicPlan

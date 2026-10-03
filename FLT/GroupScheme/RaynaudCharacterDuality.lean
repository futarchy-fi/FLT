/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterTranspose

/-!
# Perfect pairing on character summands

Restriction identifies the transpose character summand with the full linear
dual of the original character summand. The inverse extends a functional
by the actual character projector.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterProjector

variable {R G V : Type*} [CommRing R] [CommGroup G] [AddCommGroup V] [Module R V]
  [Fintype G] [Invertible (Fintype.card G : R)]
  (ρ : Representation R G V) (χ : G →* Rˣ)

/-- The transpose eigenspace is the full dual of the original eigenspace. -/
def duality : eigenspace (transpose ρ) χ ≃ₗ[R] Module.Dual R (eigenspace ρ χ) where
  toFun φ := φ.val.comp (eigenspace ρ χ).subtype
  invFun f := ⟨f.comp ((projector ρ χ).codRestrict _ (projector_mem ρ χ)), by
    apply (mem_eigenspace_iff (transpose ρ) χ _).mpr
    intro g
    ext v
    change f ⟨projector ρ χ (ρ g v), _⟩ = (χ g : R) • f ⟨projector ρ χ v, _⟩
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    exact projector_scalar ρ χ g v⟩
  left_inv φ := by
    apply Subtype.ext
    ext v
    exact transpose_pair_projector ρ χ φ v
  right_inv f := by
    ext x
    change f ⟨projector ρ χ x, _⟩ = f x
    congr 1
    apply Subtype.ext
    exact projector_eq_self ρ χ x x.property
  map_add' f g := by ext x; rfl
  map_smul' r f := by ext x; rfl

/-- The perfect pairing is ordinary evaluation on the original vectors. -/
@[simp] theorem duality_apply (φ : eigenspace (transpose ρ) χ) (x : eigenspace ρ χ) :
    duality ρ χ φ x = φ.val x := rfl

end ThreeAdicPlan.CharacterProjector

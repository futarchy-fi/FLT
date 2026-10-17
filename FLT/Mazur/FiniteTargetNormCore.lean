/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTargetAffineNorm

/-!
# Affine norm cores inside actual finite target neighborhoods

A scalar on the original source is pulled along the second endpoint over an
arbitrary affine finite target domain. The norm cuts out an affine open whose
points satisfy the scalar condition on the entire original first fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteTargetNormCore
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p q : D ⟶ A) [Flat p] [LocallyOfFinitePresentation p]
  (U : A.affineOpens) (hU : U.1 ≤ finiteTargetOpen p) (s : Γ(A, ⊤))

/-- The local norm uses the whole original relation over the affine target domain. -/
def scalar : Γ(U.1, ⊤) :=
  FiniteTargetAffineNorm.norm p U hU (((p ⁻¹ᵁ U.1).ι ≫ q).appTop s)

/-- The norm open viewed in the unchanged ambient source. -/
def core : A.Opens := U.1.ι ''ᵁ U.1.toScheme.basicOpen (scalar p q U hU s)

/-- Every constructed core is affine, even when the entire finite locus is not. -/
theorem core_isAffine : IsAffineOpen (core p q U hU s) :=
  ((isAffineOpen_top U.1.toScheme).basicOpen _).image_of_isOpenImmersion U.1.ι

/-- The norm core stays inside its actual affine target domain. -/
theorem core_le : core p q U hU s ≤ U.1 := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

/-- The local norm tests the entire original fiber, including arrows leaving the domain. -/
theorem mem_core_iff (x : A) : x ∈ core p q U hU s ↔
    x ∈ U.1 ∧ ∀ z : D, p z = x → q z ∈ A.basicOpen s := by
  have hres (z : (p ⁻¹ᵁ U.1).toScheme) :
      U.1.ι ((p ∣_ U.1) z) = p ((p ⁻¹ᵁ U.1).ι z) :=
    congrArg (fun f : (p ⁻¹ᵁ U.1).toScheme ⟶ A ↦ f z) (morphismRestrict_ι p U.1)
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, fun z hz ↦ ?_⟩
    let z' : (p ⁻¹ᵁ U.1).toScheme := ⟨z, by
      change p z ∈ U.1
      rw [hz]
      exact y.property⟩
    have he : (p ∣_ U.1) z' = y := Subtype.ext ((hres z').trans hz)
    have ht := (FiniteTargetAffineNorm.mem_basicOpen_norm_iff p U hU _ y).mp hy z' he
    rw [← Scheme.preimage_basicOpen_top] at ht
    exact ht
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply (FiniteTargetAffineNorm.mem_basicOpen_norm_iff p U hU _ ⟨x, hx⟩).mpr
    intro z hz
    rw [← Scheme.preimage_basicOpen_top]
    exact h _ ((hres z).symm.trans (congrArg U.1.ι hz))

end FLT.Mazur.FiniteTargetNormCore

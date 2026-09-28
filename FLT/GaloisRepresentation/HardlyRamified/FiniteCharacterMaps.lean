/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.FiniteCharacterDual

/-!
# Maps and exactness of finite geometric character groups

Precomposition is equivariant for the contragredient action. Characters
trivial on the kernel of a surjection factor through its quotient, giving
exactness at the middle character group without a choice of splitting.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan.FiniteContinuousGaloisModule

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

variable {A B C : FiniteContinuousGaloisModule}

/-- Pullback of geometric characters along an equivariant additive map. -/
def characterMap (f : A →+[Γ] B) : B.characterDual →+[Γ] A.characterDual where
  toFun φ := Additive.ofMul (φ.toMul.comp f.toAddMonoidHom.toMultiplicative)
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' σ φ := by
    apply MonoidHom.ext
    intro a
    change σ • φ.toMul (Multiplicative.ofAdd (σ⁻¹ • f a.toAdd)) =
      σ • φ.toMul (Multiplicative.ofAdd (f (σ⁻¹ • a.toAdd)))
    rw [map_smul f]

/-- Pullback of a character evaluates by precomposition on the original point groups. -/
@[simp] theorem characterMap_apply (f : A →+[Γ] B) (φ : B.characterDual) (a : A) :
    (characterMap f φ).toMul (Multiplicative.ofAdd a) =
      φ.toMul (Multiplicative.ofAdd (f a)) := rfl

/-- Characters pull back injectively along a surjection. -/
theorem characterMap_injective (f : A →+[Γ] B) (hf : Function.Surjective f) :
    Function.Injective (characterMap f) := by
  intro φ ψ h
  apply MonoidHom.ext
  intro b
  obtain ⟨a, ha⟩ := hf b.toAdd
  have he := congrArg (fun χ : A.characterDual ↦ χ.toMul (Multiplicative.ofAdd a)) h
  change φ.toMul (Multiplicative.ofAdd (f a)) =
    ψ.toMul (Multiplicative.ofAdd (f a)) at he
  rw [ha] at he
  exact he

/-- Dualizing an exact point sequence is exact at the middle character group. -/
theorem characterMap_exact (f : A →+[Γ] B) (g : B →+[Γ] C)
    (hg : Function.Surjective g) (hex : ∀ b, g b = 0 ↔ ∃ a, f a = b)
    (φ : B.characterDual) :
    characterMap f φ = 0 ↔ ∃ ψ : C.characterDual, characterMap g ψ = φ := by
  constructor
  · intro hφ
    let gm := g.toAddMonoidHom.toMultiplicative
    have hgm : Function.Surjective gm := by
      intro c
      obtain ⟨b, hb⟩ := hg c.toAdd
      exact ⟨Multiplicative.ofAdd b, congrArg Multiplicative.ofAdd hb⟩
    have hk : gm.ker ≤ φ.toMul.ker := by
      intro b hb
      have hb' : g b.toAdd = 0 := congrArg Multiplicative.toAdd hb
      obtain ⟨a, ha⟩ := (hex b.toAdd).mp hb'
      have he := congrArg (fun χ : A.characterDual ↦ χ.toMul (Multiplicative.ofAdd a)) hφ
      change φ.toMul b = 1
      change φ.toMul (Multiplicative.ofAdd (f a)) = 1 at he
      rw [ha] at he
      exact he
    refine ⟨Additive.ofMul (gm.liftOfSurjective hgm ⟨φ.toMul, hk⟩), ?_⟩
    apply MonoidHom.ext
    intro b
    exact gm.liftOfRightInverse_comp_apply (Function.surjInv hgm)
      (Function.rightInverse_surjInv hgm) ⟨φ.toMul, hk⟩ b
  · rintro ⟨ψ, rfl⟩
    apply MonoidHom.ext
    intro a
    have hz : g (f a.toAdd) = 0 := (hex (f a.toAdd)).mpr ⟨a.toAdd, rfl⟩
    change ψ.toMul (Multiplicative.ofAdd (g (f a.toAdd))) = 1
    rw [hz]
    exact (show C.Characters from ψ).map_one

/-- An exponent bound on a point group is inherited by its full character group. -/
theorem characterDual_nsmul (n : ℕ) (h : ∀ a : A, n • a = 0) (φ : A.characterDual) :
    n • φ = 0 := by
  apply MonoidHom.ext
  intro a
  change φ.toMul a ^ n = 1
  rw [← map_pow]
  change φ.toMul (Multiplicative.ofAdd (n • a.toAdd)) = 1
  rw [h]
  exact (show A.Characters from φ).map_one

end ThreeAdicPlan.FiniteContinuousGaloisModule

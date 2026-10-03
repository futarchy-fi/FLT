/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.CharacterBasis
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Discrete scalar extensions of character coefficients

The action is multiplication by a character defined over the smaller field.
Coordinates in any finite basis therefore intertwine the action componentwise.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {F G : Type*} [Field F] [Group G]

/-- A discrete character line over an extension of the character's field. -/
def CharacterModule (_χ : G →* Fˣ) (k : Type*) := k

variable (χ : G →* Fˣ) (k : Type*) [Field k] [Algebra F k]

instance : AddCommGroup (CharacterModule χ k) := inferInstanceAs (AddCommGroup k)
instance : Module k (CharacterModule χ k) := inferInstanceAs (Module k k)
instance : Module F (CharacterModule χ k) := inferInstanceAs (Module F k)
instance : TopologicalSpace (CharacterModule χ k) := ⊥
instance : DiscreteTopology (CharacterModule χ k) := ⟨rfl⟩

instance : DistribMulAction G (CharacterModule χ k) where
  smul g x := algebraMap F k (χ g : F) * (show k from x)
  one_smul x := by
    change algebraMap F k (χ 1 : F) * (show k from x) = x
    dsimp [CharacterModule] at x ⊢
    simp
  mul_smul g h x := by
    change algebraMap F k (χ (g * h) : F) * (show k from x) =
      algebraMap F k (χ g : F) * (algebraMap F k (χ h : F) * (show k from x))
    dsimp [CharacterModule] at x ⊢
    simp [mul_assoc]
  smul_zero g := by change (algebraMap F k (χ g : F)) * (0 : k) = 0; exact mul_zero _
  smul_add g x y := by
    change (algebraMap F k (χ g : F)) * ((show k from x) + (show k from y)) = _
    dsimp [CharacterModule] at x y ⊢
    exact mul_add _ _ _

instance : SMulCommClass G k (CharacterModule χ k) where
  smul_comm g a x := by
    change algebraMap F k (χ g : F) * (a * (show k from x)) =
      a * (algebraMap F k (χ g : F) * (show k from x))
    dsimp [CharacterModule] at x ⊢
    ring

instance : SMulCommClass G F (CharacterModule χ k) where
  smul_comm g a x := by
    change algebraMap F k (χ g : F) * (a • (show k from x)) =
      a • (algebraMap F k (χ g : F) * (show k from x))
    dsimp [CharacterModule] at x ⊢
    simp only [Algebra.smul_def, mul_left_comm]

/-- The coefficient inclusion, before passing to cocycles. -/
def characterCoefficientInclusion : CharacterModule χ F →ₗ[F] CharacterModule χ k :=
  (Algebra.linearMap F k)

/-- Inclusion of the character's field commutes with its action. -/
theorem characterCoefficientInclusion_equivariant (g : G) (x : CharacterModule χ F) :
    characterCoefficientInclusion χ k (g • x) = g • characterCoefficientInclusion χ k x := by
  change algebraMap F k ((χ g : F) * (show F from x)) =
    algebraMap F k (χ g : F) * algebraMap F k x
  dsimp [CharacterModule] at x ⊢
  exact map_mul (algebraMap F k) _ _

variable {k} {ι : Type*} [Fintype ι] (b : Module.Basis ι F k)

/-- A coefficient basis identifies the extended line with finitely many prime lines. -/
noncomputable def characterBasisCoordinates :
    CharacterModule χ k ≃ₗ[F] (ι → CharacterModule χ F) := b.equivFun

/-- The basis coordinates intertwine the character action. -/
theorem characterBasisCoordinates_equivariant (g : G) (x : CharacterModule χ k) :
    characterBasisCoordinates χ b (g • x) = g • characterBasisCoordinates χ b x := by
  ext i
  change b.equivFun (algebraMap F k (χ g : F) * (show k from x)) i =
    algebraMap F F (χ g : F) * b.equivFun (show k from x) i
  dsimp [CharacterModule] at x ⊢
  rw [← Algebra.smul_def, map_smul]
  rfl

end GaloisRepresentation.Extensions

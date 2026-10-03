/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterCoordinates

/-!
# Rank bound for integral character eigenspaces

The actual integral eigenspace injects into its generic character-function
module. Fraction-field rank invariance and generic proportionality give
rank at most one, independently of any presentation.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open CharacterProjector

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field F]
  (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))

/-- The actual integral character eigenspace of the augmentation ideal. -/
abbrev FF.integralCharacter (χ : Fˣ →* Rˣ) : Submodule R X.augmentation :=
  eigenspace (X.augmentationRepresentation lift h1 hmul) χ

omit [PerfectField K] [IsFractionRing R K] [Module F X.Points] in
/-- The integral eigenvalue equation holds on underlying coordinates. -/
theorem FF.integralCharacter_scalar (χ : Fˣ →* Rˣ)
    (a : X.integralCharacter lift h1 hmul χ) (u : Fˣ) :
    lift u (a.val : X.CoordinateRing) = (χ u : R) • (a.val : X.CoordinateRing) := by
  have h := (mem_eigenspace_iff _ χ a.val).mp a.property u
  exact congrArg (fun x : X.augmentation ↦ (x : X.CoordinateRing)) h

/-- Generic evaluation embeds each integral character space in a rank-one function space. -/
theorem FF.integralCharacter_rank_le_one (hdim : Module.finrank F X.Points = 1)
    (hlift : ∀ a x, genericHom (lift a) x = a • x) (χ : Fˣ →* Rˣ) :
    Module.rank R (X.integralCharacter lift h1 hmul χ) ≤ 1 := by
  let ψ : Fˣ →* Kˣ := (Units.map (algebraMap R K).toMonoidHom).comp χ
  let P := CharacterRank.functions (V := X.Points) (L := AlgebraicClosure K) ψ
  let j : X.integralCharacter lift h1 hmul χ →ₗ[R] P :=
    ((X.characterCoordinates.toLinearMap.comp X.augmentation.subtype).comp
      (X.integralCharacter lift h1 hmul χ).subtype).codRestrict
        (P.restrictScalars R) (by
          intro a
          constructor
          · change X.characterCoordinates (a.val : X.CoordinateRing) 0 = 0
            rw [X.characterCoordinates_counit, a.val.property, map_zero]
          · intro u x
            change X.characterCoordinates (a.val : X.CoordinateRing) ((u : F) • x) = _
            rw [← hlift, ← ModelHom.characterCoordinates_apply,
              X.integralCharacter_scalar lift h1 hmul χ a u, map_smul]
            change (MulActionHom.evalAlgHom
              (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) R X.Points
              (AlgebraicClosure K) x) ((χ u : R) •
                X.characterCoordinates (a.val : X.CoordinateRing)) = _
            rw [map_smul, Algebra.smul_def]
            change algebraMap R (AlgebraicClosure K) (χ u) *
              X.characterCoordinates (a.val : X.CoordinateRing) x = _
            rw [IsScalarTower.algebraMap_apply R K (AlgebraicClosure K)]
            rfl)
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    apply X.characterCoordinates_injective
    exact congrArg Subtype.val h
  calc
    Module.rank R (X.integralCharacter lift h1 hmul χ) ≤ Module.rank R P :=
      j.rank_le_of_injective hj
    _ = Module.rank K P := (IsFractionRing.rank_right_eq R K P).symm
    _ ≤ 1 := CharacterRank.functions_rank_le_one hdim ψ

end ThreeAdicPlan

/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryDSexticQuotient
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The mod-three cyclotomic character on the augmented quotient

The Kummer point kernel fixes every cube root of unity, so the actual
mod-three cyclotomic character factors through the augmented point quotient.
It is nontrivial because a primitive cube root of unity is not rational.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- The mod-three cyclotomic character, defined by its action on cube roots of unity. -/
def modThreeCyclotomic : Γ →* (ZMod 3)ˣ :=
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) 3)).comp
    { toFun := fun σ ↦ σ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

/-- The defining action of the mod-three cyclotomic character. -/
theorem modThreeCyclotomic_spec (σ : Γ) (x : AlgebraicClosure ℚ) (hx : x ^ 3 = 1) :
    σ x = x ^ (modThreeCyclotomic σ : ZMod 3).val := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  let u := Units.mk0 x hx0
  exact modularCyclotomicCharacter.spec _ _ σ.toRingEquiv
    ((mem_rootsOfUnity' 3 u).mpr hx)

/-- The rational mod-three cyclotomic character is nontrivial. -/
theorem modThreeCyclotomic_ne_one : modThreeCyclotomic ≠ 1 := by
  intro h
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 3
  have hfixed : ∀ σ : Γ, σ ζ = ζ := by
    intro σ
    simpa [h, ZMod.val_one] using modThreeCyclotomic_spec σ ζ hζ.pow_eq_one
  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed ζ).mpr hfixed
  have hqpow : q ^ 3 = (1 : ℚ) := by
    apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    simpa [map_pow, hq] using hζ.pow_eq_one
  have hqone : q = 1 := (Odd.pow_injective (by decide : Odd 3)) (by simpa using hqpow)
  apply hζ.ne_one (by decide)
  rw [← hq, hqone, map_one]

/-- Fixing all augmented points forces the mod-three cyclotomic character to be one. -/
theorem augmentedPointKernel_le_modThreeCyclotomic_ker (H : FiniteFlatObject ZInvTwo) :
    (augmentedObject H).points.pointActionKernel ≤ modThreeCyclotomic.ker := by
  intro σ hσ
  have hk : σ ∈ kummerTwoPoints.pointActionKernel := by
    change σ ∈ (H.points.prod kummerTwoPoints).pointActionKernel at hσ
    rw [FiniteContinuousGaloisModule.pointActionKernel_prod] at hσ
    exact hσ.2
  rw [MonoidHom.mem_ker]
  apply Units.ext
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  change σ (t : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ) ^ (1 : ZMod 3).val
  have hfix := fixes_kummerTwoRoots_of_fixes_cubeRoots σ
    ((mem_kummerTwoPointActionKernel σ).mp hk) 0 t
    (by simpa using (mem_rootsOfUnity' 3 t).mp ht)
  simpa [ZMod.val_one] using hfix

/-- The mod-three cyclotomic character on the actual augmented point quotient. -/
def augmentedModThreeCyclotomic (H : FiniteFlatObject ZInvTwo) :
    AugmentedPointGaloisGroup H →* (ZMod 3)ˣ :=
  QuotientGroup.lift _ modThreeCyclotomic (augmentedPointKernel_le_modThreeCyclotomic_ker H)

/-- Pullback of the quotient cyclotomic character is the usual cyclotomic character. -/
theorem augmentedModThreeCyclotomic_apply (H : FiniteFlatObject ZInvTwo) (σ : Γ) :
    augmentedModThreeCyclotomic H (QuotientGroup.mk' _ σ) = modThreeCyclotomic σ := rfl

/-- The cyclotomic character remains nontrivial on the augmented point quotient. -/
theorem augmentedModThreeCyclotomic_ne_one (H : FiniteFlatObject ZInvTwo) :
    augmentedModThreeCyclotomic H ≠ 1 := by
  intro h
  apply modThreeCyclotomic_ne_one
  apply MonoidHom.ext
  intro σ
  exact congrArg (fun f : AugmentedPointGaloisGroup H →* (ZMod 3)ˣ ↦
    f (QuotientGroup.mk' _ σ)) h

end ThreeAdicPlan

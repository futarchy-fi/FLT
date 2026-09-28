/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PureAction
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The character dual of a finite rational Galois module

The geometric character dual consists of all homomorphisms to algebraic roots
of unity, with the contragredient Galois action. Characters separate points.
This constructs the point module only; it does not construct a Cartier dual
of an integral finite-flat model.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan
namespace FiniteContinuousGaloisModule

/-- The multiplicative characters of a finite additive point module. -/
abbrev Characters (W : FiniteContinuousGaloisModule) :=
  Multiplicative W →* (AlgebraicClosure ℚ)ˣ

/-- Galois conjugation of a character acts on both its source and its values. -/
def conjugateCharacter (W : FiniteContinuousGaloisModule)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (φ : W.Characters) : W.Characters where
  toFun w := σ • φ (Multiplicative.ofAdd (σ⁻¹ • w.toAdd))
  map_one' := by simp
  map_mul' x y := by
    change σ • φ (Multiplicative.ofAdd (σ⁻¹ • (x.toAdd + y.toAdd))) = _
    rw [smul_add, ofAdd_add, map_mul, smul_mul']

/-- The contragredient action on the additive character group. -/
instance characterAction (W : FiniteContinuousGaloisModule) :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Additive W.Characters) where
  smul σ φ := Additive.ofMul (W.conjugateCharacter σ φ.toMul)
  one_smul φ := by
    change W.conjugateCharacter 1 φ.toMul = φ.toMul
    apply MonoidHom.ext
    intro w
    simp [conjugateCharacter]
  mul_smul σ τ φ := by
    change W.conjugateCharacter (σ * τ) φ.toMul =
      W.conjugateCharacter σ (W.conjugateCharacter τ φ.toMul)
    apply MonoidHom.ext
    intro w
    simp [conjugateCharacter, mul_smul]
  smul_zero σ := by
    change W.conjugateCharacter σ 1 = 1
    apply MonoidHom.ext
    intro w
    simp [conjugateCharacter]
  smul_add σ φ ψ := by
    change W.conjugateCharacter σ (φ.toMul * ψ.toMul) =
      W.conjugateCharacter σ φ.toMul * W.conjugateCharacter σ ψ.toMul
    apply MonoidHom.ext
    intro w
    simp [conjugateCharacter, smul_mul']

/-- The character action evaluates by conjugating values and acting inversely
on the source. -/
theorem characterAction_apply (W : FiniteContinuousGaloisModule)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (φ : Additive W.Characters) (w : W) :
    (σ • φ).toMul (Multiplicative.ofAdd w) =
      σ • φ.toMul (Multiplicative.ofAdd (σ⁻¹ • w)) := rfl

/-- Characters with algebraic values separate points of a finite group. -/
theorem characters_separate (W : FiniteContinuousGaloisModule) {x y : W}
    (h : ∀ φ : W.Characters, φ (Multiplicative.ofAdd x) = φ (Multiplicative.ofAdd y)) :
    x = y :=
  (CommGroup.forall_apply_eq_apply_iff (Multiplicative W) (M := AlgebraicClosure ℚ)).mp h

/-- Character conjugation is continuous for the discrete topology. -/
instance characterContinuous (W : FiniteContinuousGaloisModule) :
    ContinuousSMulDiscrete (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (Additive W.Characters) where
  isOpen_smul_eq φ ψ := by
    have he : {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | σ • φ = ψ} =
        ⋂ w : W, ⋃ a : W,
          {σ | σ⁻¹ • w = a} ∩
          {σ | σ • (φ.toMul (Multiplicative.ofAdd a) : AlgebraicClosure ℚ) =
            (ψ.toMul (Multiplicative.ofAdd w) : AlgebraicClosure ℚ)} := by
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h w
        refine ⟨σ⁻¹ • w, rfl, ?_⟩
        exact congrArg (fun χ : Additive W.Characters ↦
          (χ.toMul (Multiplicative.ofAdd w) : AlgebraicClosure ℚ)) h
      · intro h
        apply MonoidHom.ext
        intro w
        obtain ⟨a, ha, he⟩ := h w.toAdd
        apply Units.ext
        change σ • (φ.toMul (Multiplicative.ofAdd (σ⁻¹ • w.toAdd)) :
          AlgebraicClosure ℚ) = _
        rw [ha]
        exact he
    rw [he]
    apply isOpen_iInter_of_finite
    intro w
    apply isOpen_iUnion
    intro a
    exact ((ContinuousSMulDiscrete.isOpen_smul_eq _ w a).preimage continuous_inv).inter
      (ContinuousSMulDiscrete.isOpen_smul_eq _ _ _)

/-- The finite continuous Galois module of all geometric characters. -/
abbrev characterDual (W : FiniteContinuousGaloisModule) : FiniteContinuousGaloisModule :=
  { Carrier := Additive W.Characters }

/-- The evaluation pairing of the geometric character dual is equivariant. -/
theorem characterDual_eval_smul (W : FiniteContinuousGaloisModule)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (φ : W.characterDual) (w : W) :
    (σ • φ).toMul (Multiplicative.ofAdd (σ • w)) =
      σ • φ.toMul (Multiplicative.ofAdd w) := by
  change σ • φ.toMul (Multiplicative.ofAdd (σ⁻¹ • σ • w)) = _
  rw [inv_smul_smul]

end FiniteContinuousGaloisModule
end ThreeAdicPlan

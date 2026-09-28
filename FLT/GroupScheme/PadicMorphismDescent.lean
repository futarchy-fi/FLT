/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicTensorPatching
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent of prescribed algebra morphisms

Compatible algebra maps over `ℤ[1/(dp)]` and `ℤ_p` descend uniquely to the
specified global algebras over `ℤ[1/d]`. Only the target coordinate algebra
needs to be finite projective. The construction uses the arithmetic
intersection of the scalar extensions of that actual algebra, so it does
not replace either global model by a newly patched object.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.PadicPatching

variable (p : ℕ) [Fact p.Prime] (d : ℤ) [Fact (¬ (p : ℤ) ∣ d)]

/-- The global coefficient ring embeds in the ring with `p` additionally inverted. -/
theorem baseToAway_injective : Function.Injective (algebraMap (Base d) (Away d p)) := by
  let : NeZero d := ⟨denominator_ne_zero p d⟩
  apply IsLocalization.injective (M := Submonoid.powers (p : Base d)) (Away d p)
  rintro x ⟨n, rfl⟩
  apply pow_mem
  apply mem_nonZeroDivisors_of_ne_zero
  intro hp
  have hq : (p : ℚ_[p]) = 0 := by
    simpa using congrArg (algebraMap (Base d) ℚ_[p]) hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hq

variable (A B : Type) [CommRing A] [CommRing B]
    [Algebra (Base d) A] [Algebra (Base d) B]
    [Module.Finite (Base d) B] [Module.Projective (Base d) B]

omit [Module.Finite (Base d) B] in
/-- Equality of global algebra maps can be checked after inverting `p`. -/
theorem algHom_ext_away {f g : A →ₐ[Base d] B}
    (h : ∀ a, (1 : Away d p) ⊗ₜ[Base d] f a = 1 ⊗ₜ[Base d] g a) : f = g := by
  ext a
  exact Algebra.TensorProduct.includeRight_injective (baseToAway_injective p d) (h a)

/-- Compatible prescribed away and local algebra maps have a unique global
extension. Compatibility is required only on global generators. -/
theorem existsUnique_algHom_of_away_local
    (fAway : Away d p ⊗[Base d] A →ₐ[Away d p] Away d p ⊗[Base d] B)
    (fLocal : ℤ_[p] ⊗[Base d] A →ₐ[ℤ_[p]] ℤ_[p] ⊗[Base d] B)
    (h : ∀ a : A,
      scalarExtensionMap (Away d p) ℚ_[p] B (fAway (1 ⊗ₜ[Base d] a)) =
        scalarExtensionMap ℤ_[p] ℚ_[p] B (fLocal (1 ⊗ₜ[Base d] a))) :
    ∃! f : A →ₐ[Base d] B,
      (∀ a, (1 : Away d p) ⊗ₜ[Base d] f a = fAway (1 ⊗ₜ[Base d] a)) ∧
      (∀ a, (1 : ℤ_[p]) ⊗ₜ[Base d] f a = fLocal (1 ⊗ₜ[Base d] a)) := by
  have hex (a : A) : ∃ b : B, (1 : Away d p) ⊗ₜ[Base d] b =
      fAway (1 ⊗ₜ[Base d] a) :=
    (scalarExtension_intersection p d B _).2 ⟨fLocal (1 ⊗ₜ[Base d] a), h a⟩
  choose f hf using hex
  let jA : A →ₐ[Base d] Away d p ⊗[Base d] A := Algebra.TensorProduct.includeRight
  let jB : B →ₐ[Base d] Away d p ⊗[Base d] B := Algebra.TensorProduct.includeRight
  have hj : Function.Injective jB :=
    Algebra.TensorProduct.includeRight_injective (baseToAway_injective p d)
  have hf' (a : A) : jB (f a) = fAway (jA a) := hf a
  let F : A →ₐ[Base d] B :=
    { toFun := f
      map_zero' := hj (by simp only [hf', map_zero])
      map_one' := hj (by simp only [hf', map_one])
      map_add' := fun a b ↦ hj (by simp only [hf', map_add])
      map_mul' := fun a b ↦ hj (by simp only [hf', map_mul])
      commutes' := fun r ↦ hj (by simp only [hf', AlgHom.commutes,
        IsScalarTower.algebraMap_apply (Base d) (Away d p) (Away d p ⊗[Base d] A),
        IsScalarTower.algebraMap_apply (Base d) (Away d p) (Away d p ⊗[Base d] B)]) }
  have hloc (a : A) : (1 : ℤ_[p]) ⊗ₜ[Base d] F a = fLocal (1 ⊗ₜ[Base d] a) := by
    have hinj : Function.Injective (scalarExtensionMap ℤ_[p] ℚ_[p] B (R := Base d)) :=
      Module.Flat.rTensor_preserves_injective_linearMap
        (IsScalarTower.toAlgHom (Base d) ℤ_[p] ℚ_[p]).toLinearMap
        (IsFractionRing.injective ℤ_[p] ℚ_[p])
    apply hinj
    rw [scalarExtensionMap_tmul, map_one, ← h]
    rw [← hf a, scalarExtensionMap_tmul, map_one]
    rfl
  exact ⟨F, ⟨hf, hloc⟩, fun g hg ↦ algHom_ext_away p d A B
    (fun a ↦ (hg.1 a).trans (hf a).symm)⟩

end ThreeAdicPlan.PadicPatching

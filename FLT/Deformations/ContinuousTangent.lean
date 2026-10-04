/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.DualNumberTest

/-!
# Continuous tangent functionals and dual-number parameters

The tangent space consists of continuous coefficient-linear Leibniz
functionals at the specified residue map. It is identified with the actual
maps to the finite dual-number test object.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing TrivSqZeroExt

namespace Deformation.ProartinianCat

variable (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
  (A : ProartinianCat O)

local notation "k" => residueField (𝓞 := O)
local notation "ε₀" => Hom.hom (toResidueField A)

/-- Continuous relative tangent functionals at the original residue map. -/
def continuousTangent : Submodule k (A →L[O] k) where
  carrier := {d | d 1 = 0 ∧ ∀ a b, d (a * b) = ε₀ a * d b + ε₀ b * d a}
  zero_mem' := by simp
  add_mem' := by
    intro d e hd he
    constructor
    · simp [hd.1, he.1]
    · intro a b
      simp only [add_apply, hd.2, he.2]
      ring
  smul_mem' := by
    intro c d hd
    constructor
    · simp [hd.1]
    · intro a b
      simp only [smul_apply, smul_eq_mul, hd.2]
      ring

/-- A tangent functional gives its dual-number coefficient map. -/
def tangentToDualNumber (d : continuousTangent O A) : A ⟶ dualNumberTest O where
  hom :=
    { toFun := fun a ↦ ⟨ε₀ a, d.1 a⟩
      map_zero' := by apply TrivSqZeroExt.ext <;> simp
      map_one' := by apply TrivSqZeroExt.ext <;> simp [d.2.1]
      map_add' := by intro a b; apply TrivSqZeroExt.ext <;> simp
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · exact map_mul ε₀ a b
        · change d.1 (a * b) = ε₀ a * d.1 b + d.1 a * ε₀ b
          rw [mul_comm (d.1 a)]
          exact d.2.2 a b
      commutes' := by
        intro o
        apply TrivSqZeroExt.ext
        · exact (Hom.hom (toResidueField A)).commutes o
        · change d.1 (algebraMap O A o) = 0
          rw [Algebra.algebraMap_eq_smul_one, map_smul, d.2.1, smul_zero]
      cont := (Hom.hom (toResidueField A)).cont.prodMk d.1.continuous }

/-- A dual-number map is determined by its tangent functional. -/
theorem tangentToDualNumber_injective : Function.Injective (tangentToDualNumber O A) := by
  intro d e h
  apply Subtype.ext
  ext a
  exact congrArg (fun f : A ⟶ dualNumberTest O ↦ (f.hom a).snd) h

/-- Every dual-number map has the specified residue component. -/
theorem dualNumberHom_fst (f : A ⟶ dualNumberTest O) (a : A) :
    (f.hom a).fst = ε₀ a := by
  let g : A ⟶ k := ⟨⟨(fstHom O k k).comp f.hom.toAlgHom,
    TrivSqZeroExt.continuous_fst.comp f.hom.cont⟩⟩
  exact congrArg (fun h : A ⟶ k ↦ h.hom a) (Subsingleton.elim g (toResidueField A))

/-- Taking the epsilon coefficient produces a continuous relative tangent functional. -/
def dualNumberToTangent (f : A ⟶ dualNumberTest O) : continuousTangent O A := by
  refine ⟨{ toLinearMap := (sndHom k k).restrictScalars O ∘ₗ f.hom.toAlgHom.toLinearMap
            cont := TrivSqZeroExt.continuous_snd.comp f.hom.cont }, ?_⟩
  constructor
  · change (f.hom 1).snd = 0
    rw [map_one, snd_one]
  · intro a b
    change (f.hom (a * b)).snd = ε₀ a * (f.hom b).snd + ε₀ b * (f.hom a).snd
    rw [map_mul]
    change (f.hom a).fst * (f.hom b).snd + (f.hom a).snd * (f.hom b).fst = _
    rw [dualNumberHom_fst O A f a, dualNumberHom_fst O A f b, mul_comm (f.hom a).snd]

/-- Dual-number parameters are precisely the continuous tangent functionals. -/
def continuousTangentEquiv : continuousTangent O A ≃ (A ⟶ dualNumberTest O) where
  toFun := tangentToDualNumber O A
  invFun := dualNumberToTangent O A
  left_inv d := by apply Subtype.ext; ext; rfl
  right_inv f := by
    apply Hom.ext
    apply ContinuousAlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · exact (dualNumberHom_fst O A f a).symm
    · rfl

/-- Finiteness of the dual-number parameters gives a finite continuous tangent space. -/
theorem finite_continuousTangent [Finite (A ⟶ dualNumberTest O)] :
    Finite (continuousTangent O A) :=
  Finite.of_injective _ (tangentToDualNumber_injective O A)

end Deformation.ProartinianCat

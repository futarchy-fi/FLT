/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicGenerator

/-!
# Maps from the constant cyclic group scheme

A homomorphism from the finite cyclic group into scheme sections determines
an actual group-scheme morphism. Its restrictions to all components are the
given sections, so this construction retains the prescribed generator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open CartesianMonoidalCategory

namespace FLT.Mazur.ConstantCyclicSectionMap

universe u
variable {S : Scheme.{u}} {n : ℕ} [NeZero n] {G : Over S} [GrpObj G]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ G))

/-- Descend the prescribed sections along the actual coproduct of the base. -/
def toScheme : ConstantCyclicGroup.model S n ⟶ G :=
  Sigma.desc fun i ↦ φ (Multiplicative.ofAdd i)

omit [NeZero n] in
/-- Every component maps by its prescribed section. -/
@[reassoc (attr := simp)]
theorem component_toScheme (i : ZMod n) :
    ConstantCyclicGroup.component S n i ≫ toScheme φ = φ (Multiplicative.ofAdd i) :=
  Sigma.ι_comp_desc _ _

/-- The descended scheme map preserves the group operations. -/
instance toScheme_isMonHom : IsMonHom (toScheme φ) where
  one_hom := by
    change ConstantCyclicGroup.identity S n ≫ toScheme φ = η[G]
    rw [ConstantCyclicGroup.identity, Category.assoc, component_toScheme]
    change η[𝟙_ (Over S)] ≫ φ 1 = η[G]
    simp [Hom.one_def]
  mul_hom := by
    change ConstantCyclicGroup.multiplication S n ≫ toScheme φ =
      (toScheme φ ⊗ₘ toScheme φ) ≫ μ[G]
    apply PolygonSplitGroup.tensor_hom_ext
      (fun _ : ZMod n ↦ 𝟙_ (Over S)) (fun _ : ZMod n ↦ 𝟙_ (Over S))
    intro i j
    change (ConstantCyclicGroup.component S n i ⊗ₘ
      ConstantCyclicGroup.component S n j) ≫ _ = _
    rw [ConstantCyclicGroup.component_multiplication_assoc, component_toScheme,
      tensorHom_comp_tensorHom_assoc, component_toScheme, component_toScheme]
    change μ[𝟙_ (Over S)] ≫ φ (Multiplicative.ofAdd i * Multiplicative.ofAdd j) = _
    rw [map_mul, Hom.mul_def]
    rw [← Category.assoc]
    congr 1
    apply hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst]
      exact congrArg (fun f ↦ f ≫ φ (Multiplicative.ofAdd i)) (Subsingleton.elim _ _)
    · simp only [Category.assoc, lift_snd, tensorHom_snd]
      exact congrArg (fun f ↦ f ≫ φ (Multiplicative.ofAdd j)) (Subsingleton.elim _ _)

end FLT.Mazur.ConstantCyclicSectionMap

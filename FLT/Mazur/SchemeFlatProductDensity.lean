/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Schematic density in products of flat schemes

Two schematically dense morphisms give a schematically dense product map when
flatness permits the two successive base changes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.SchemeFlatProductDensity

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {U V X Y S : Scheme} (f : U ⟶ X) (g : V ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S)

/-- Changing the first factor is a base change of the original dense morphism. -/
theorem left_dense [IsSchemeTheoreticallyDominant f] [QuasiCompact f] [Flat b] :
    IsSchemeTheoreticallyDominant
      (pullback.lift (f := a) (g := b) (pullback.fst (f ≫ a) b ≫ f) (pullback.snd (f ≫ a) b)
        (by rw [Category.assoc, pullback.condition])) := by
  apply IsSchemeTheoreticallyDominant.of_isPullback (f := f) (g := pullback.fst a b)
  convert IsPullback.of_bot' (.of_hasPullback (f ≫ a) b) (.of_hasPullback a b) using 1
  apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd,
    IsPullback.lift_fst, IsPullback.lift_snd]

/-- Changing the second factor is the symmetric flat base change. -/
theorem right_dense [IsSchemeTheoreticallyDominant g] [QuasiCompact g] [Flat a] :
    IsSchemeTheoreticallyDominant
      (pullback.lift (f := a) (g := b) (pullback.fst a (g ≫ b)) (pullback.snd a (g ≫ b) ≫ g)
        (by rw [Category.assoc, pullback.condition])) := by
  apply IsSchemeTheoreticallyDominant.of_isPullback (f := g) (g := pullback.snd a b)
  convert (IsPullback.of_right' (.of_hasPullback a (g ≫ b))
    (.of_hasPullback a b)).flip using 1
  apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd,
    IsPullback.lift_fst, IsPullback.lift_snd]

/-- The actual product comparison is schematically dominant. -/
theorem product_dense [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    [IsSchemeTheoreticallyDominant g] [QuasiCompact g] [Flat a] [Flat (g ≫ b)] :
    IsSchemeTheoreticallyDominant
      (pullback.map (f ≫ a) (g ≫ b) a b f g (𝟙 S) (by simp) (by simp)) := by
  let l := pullback.lift (f := a) (g := g ≫ b) (pullback.fst (f ≫ a) (g ≫ b) ≫ f)
    (pullback.snd (f ≫ a) (g ≫ b)) (by rw [Category.assoc, pullback.condition])
  let r := pullback.lift (f := a) (g := b) (pullback.fst a (g ≫ b)) (pullback.snd a (g ≫ b) ≫ g)
    (by rw [Category.assoc, pullback.condition])
  have hl : IsSchemeTheoreticallyDominant l := left_dense f a (g ≫ b)
  have hr : IsSchemeTheoreticallyDominant r := right_dense g a b
  have he : pullback.map (f ≫ a) (g ≫ b) a b f g (𝟙 S) (by simp) (by simp) = l ≫ r := by
    apply pullback.hom_ext <;> simp only [l, r, pullback.map, pullback.lift_fst,
      pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc]
  rw [he]
  infer_instance

end FLT.Mazur.SchemeFlatProductDensity

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OpenImmersionImageUnionPullback

/-!
# Compare glued outputs on two ambient image unions

Equality on every literal cross-family intersection compares the two glued
outputs on their full ambient fiber product.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur
universe u v w
variable {X T : Scheme.{u}} {ι : Type v} {κ : Type w}
  {V : ι → Scheme.{u}} {W : κ → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) (g : ∀ j, W j ⟶ X)
  [∀ i, IsOpenImmersion (f i)] [∀ j, IsOpenImmersion (g j)]
  (a : ∀ i, V i ⟶ T) (b : ∀ j, W j ⟶ T)
  (ha : ∀ i j, pullback.fst (f i) (f j) ≫ a i = pullback.snd (f i) (f j) ≫ a j)
  (hb : ∀ i j, pullback.fst (g i) (g j) ≫ b i = pullback.snd (g i) (g j) ≫ b j)

/-- Compatible cross-family local outputs compare the two actual ambient gluings. -/
theorem openImageUnionGlue_pullback_eq
    (hab : ∀ i j, pullback.fst (f i) (g j) ≫ a i =
      pullback.snd (f i) (g j) ≫ b j) :
    pullback.fst (openImageUnion f).ι (openImageUnion g).ι ≫ openImageUnionGlue f a ha =
      pullback.snd (openImageUnion f).ι (openImageUnion g).ι ≫ openImageUnionGlue g b hb := by
  apply openImageUnionPullback_hom_ext f g
  intro i j
  rw [openImageUnionPullbackMap_fst_assoc, openImageUnionPullbackMap_snd_assoc,
    openImageUnionGlue_fac, openImageUnionGlue_fac]
  exact hab i j

/-- The same comparison holds on every common source over the ambient scheme. -/
theorem openImageUnionGlue_overlap_eq
    (hab : ∀ i j, pullback.fst (f i) (g j) ≫ a i =
      pullback.snd (f i) (g j) ≫ b j)
    {Y : Scheme.{u}} (p : Y ⟶ (openImageUnion f).toScheme)
    (q : Y ⟶ (openImageUnion g).toScheme)
    (hpq : p ≫ (openImageUnion f).ι = q ≫ (openImageUnion g).ι) :
    p ≫ openImageUnionGlue f a ha = q ≫ openImageUnionGlue g b hb := by
  have h := congrArg (pullback.lift p q hpq ≫ ·)
    (openImageUnionGlue_pullback_eq f g a b ha hb hab)
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h

end FLT.Mazur

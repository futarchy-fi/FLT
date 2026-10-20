/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OpenImmersionImageUnionGluing

/-!
# Compare a whole glued law with a single ambient open

Pulling back the actual image-union cover reduces the full comparison to the
literal intersections with its original charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {X T Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)]
  (a : ∀ i, V i ⟶ T)
  (ha : ∀ i j, pullback.fst (f i) (f j) ≫ a i = pullback.snd (f i) (f j) ≫ a j)
  (g : Y ⟶ X) (b : Y ⟶ T)

/-- Local comparisons with a single source determine the entire glued output. -/
theorem openImageUnionGlue_single_overlap
    (hab : ∀ i, pullback.fst (f i) g ≫ a i = pullback.snd (f i) g ≫ b)
    {Z : Scheme.{u}} (p : Z ⟶ (openImageUnion f).toScheme) (q : Z ⟶ Y)
    (hpq : p ≫ (openImageUnion f).ι = q ≫ g) :
    p ≫ openImageUnionGlue f a ha = q ≫ b := by
  apply Scheme.Cover.hom_ext ((openImageUnionCover f).pullback₁ p)
  intro i
  let r := pullback.fst p (openImageUnionMap f i)
  let s := pullback.snd p (openImageUnionMap f i)
  have h : r ≫ p = s ≫ openImageUnionMap f i := pullback.condition
  have hs : s ≫ f i = (r ≫ q) ≫ g := by
    rw [← openImageUnionMap_fac f i, ← Category.assoc, ← h]
    rw [Category.assoc, hpq, Category.assoc]
  have he := congrArg (pullback.lift s (r ≫ q) hs ≫ ·) (hab i)
  change r ≫ p ≫ _ = r ≫ q ≫ b
  rw [← Category.assoc, h, Category.assoc, openImageUnionGlue_fac]
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] using he

/-- The literal full intersection of the glued domain and the single source agrees. -/
theorem openImageUnionGlue_single_pullback
    (hab : ∀ i, pullback.fst (f i) g ≫ a i = pullback.snd (f i) g ≫ b) :
    pullback.fst (openImageUnion f).ι g ≫ openImageUnionGlue f a ha =
      pullback.snd (openImageUnion f).ι g ≫ b :=
  openImageUnionGlue_single_overlap f a ha g b hab _ _ pullback.condition

end FLT.Mazur

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentEffectiveRecovery

/-!
# Original effective member recoveries in named pair charts

Normalize the original counit pair equation without unfolding the effective
line bundle or the independent representatives.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard SchemeIndependentCanonicalOverlap SchemeIndependentPairNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled descended
variable {X : Scheme.{u}} {𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X}
variable (D : IndependentLineData 𝒰) (i j : 𝒰.I₀)
variable {Z : Scheme.{u}}
variable (t : Z ⟶ Limits.pullback (𝒰.f i) (𝒰.f j)) (l : Z ⟶ 𝒰.X i) (r : Z ⟶ 𝒰.X j)
variable (wl : t ≫ Limits.pullback.fst (𝒰.f i) (𝒰.f j) = l)
variable (wr : t ≫ Limits.pullback.snd (𝒰.f i) (𝒰.f j) = r)
variable (k : Z ⟶ X) (hl : l ≫ 𝒰.f i = k) (hr : r ≫ 𝒰.f j = k)

/-- Every named chart retains the original effective counit compatibility. -/
lemma descendedMemberRecovery_chart :
    (SchemeIndependentCanonicalOverlap.overlap (𝒰.f i) (𝒰.f j) l r k hl hr D.descended.val).hom ≫
        (pullback r).map (D.descendedMemberRecovery j).hom =
      (pullback l).map (D.descendedMemberRecovery i).hom ≫
        (SchemeIndependentPairNormalization.normalize (Limits.pullback.fst (𝒰.f i) (𝒰.f j))
          (Limits.pullback.snd (𝒰.f i) (𝒰.f j)) t l r wl wr
          (D.obj i).val (D.obj j).val (D.overlap (i, j))).hom := by
  have h := D.descendedMemberRecovery_pair (i, j)
  have hn := normalize_compatible (Limits.pullback.fst (𝒰.f i) (𝒰.f j))
    (Limits.pullback.snd (𝒰.f i) (𝒰.f j)) t l r wl wr
    (SchemeIndependentCanonicalOverlap.pair (𝒰.f i) (𝒰.f j) D.descended.val) (D.overlap (i, j))
    (D.descendedMemberRecovery i).hom (D.descendedMemberRecovery j).hom h
  have hc : SchemeIndependentPairNormalization.normalize (Limits.pullback.fst (𝒰.f i) (𝒰.f j))
      (Limits.pullback.snd (𝒰.f i) (𝒰.f j)) t l r wl wr
      ((pullback (𝒰.f i)).obj D.descended.val)
      ((pullback (𝒰.f j)).obj D.descended.val)
      (SchemeIndependentCanonicalOverlap.pair (𝒰.f i) (𝒰.f j) D.descended.val) =
      SchemeIndependentCanonicalOverlap.overlap (𝒰.f i) (𝒰.f j) l r k hl hr D.descended.val :=
    normalize_overlap (𝒰.f i) (𝒰.f j) (Limits.pullback.fst (𝒰.f i) (𝒰.f j))
      (Limits.pullback.snd (𝒰.f i) (𝒰.f j))
      (Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl Limits.pullback.condition.symm
      t l r wl wr k hl hr D.descended.val
  rw [hc] at hn
  exact hn

end FLT.Mazur.SchemeFppfFamily.IndependentLineData

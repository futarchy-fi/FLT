/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentEffectivePairCharts

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

/-- A named chart with a specified return retains that exact transition. -/
lemma descendedMemberRecovery_chart_of_return
    (q : (pullback l).obj (D.obj i).val ≅ (pullback r).obj (D.obj j).val)
    (hq : SchemeIndependentPairNormalization.normalize
      (Limits.pullback.fst (𝒰.f i) (𝒰.f j))
      (Limits.pullback.snd (𝒰.f i) (𝒰.f j)) t l r wl wr
      (D.obj i).val (D.obj j).val (D.overlap (i, j)) = q) :
    (SchemeIndependentCanonicalOverlap.overlap
        (𝒰.f i) (𝒰.f j) l r k hl hr D.descended.val).hom ≫
      (pullback r).map (D.descendedMemberRecovery j).hom =
    (pullback l).map (D.descendedMemberRecovery i).hom ≫ q.hom := by
  rw [← hq]
  exact D.descendedMemberRecovery_chart i j t l r wl wr k hl hr

end FLT.Mazur.SchemeFppfFamily.IndependentLineData

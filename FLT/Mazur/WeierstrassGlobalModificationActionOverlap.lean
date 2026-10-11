/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationActionFlatExt

/-!
# Compatibility on every actual action-cover intersection

Refine the full categorical intersection by affine opens. Its maps to both
source members are open immersions, hence flat. Regular-center uniqueness
then identifies the actual lifts, including two exceptional affine outputs
with different original input directions and unrelated affine presentations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassGlobalModification

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The actual local actions agree on every full scheme-theoretic source intersection. -/
theorem smoothActionLocal_overlap
    (i j : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀) :
    pullback.fst (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f i)
        (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f j) ≫
        smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i =
      pullback.snd (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f i)
        (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs |>.f j) ≫
        smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs j := by
  let C := smoothActionCover W s b3 b4 b6 h3 h4 h6 hs
  let U := pullback (C.f i) (C.f j)
  apply U.affineCover.hom_ext
  intro k
  symm
  rw [← Category.assoc]
  apply smoothActionLocal_flat_unique W s b3 b4 b6 h3 h4 h6 hs i
    (U.affineCover.f k ≫ pullback.fst (C.f i) (C.f j))
  simp only [Category.assoc]
  exact congrArg (U.affineCover.f k ≫ ·)
    (smoothActionLocal_overlap_contraction W s b3 b4 b6 h3 h4 h6 hs i j).symm

end FLT.Mazur.WeierstrassGlobalModification

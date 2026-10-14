/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothConnectedComponents

/-!
# Locate a smooth connected component by its original normalization image

Membership in a punctured normalization image determines the entire smooth
connected component of an independently given point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} [LocallyOfFinitePresentation C.hom]
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include hn q h in
/-- Membership in a specified punctured component determines the whole connected component. -/
theorem smooth_connectedComponent_image_of_mem (i : ZMod n)
    (y : C.hom.smoothLocus.toScheme)
    (hy : C.hom.smoothLocus.ι y ∈
      Set.range (torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm i) ≫ p).left) :
    C.hom.smoothLocus.ι '' connectedComponent y =
      Set.range (torusToComponent K ≫ componentι K n ((ZMod.finEquiv n).symm i) ≫ p).left := by
  obtain ⟨x, hx⟩ := hy
  have he : (smoothComponent K n hn p q h i).left x = y := by
    apply C.hom.smoothLocus.ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f x) (smoothComponent_ι K n hn p q h i)).trans hx
  rw [← he]
  exact smoothComponent_connectedComponent_image K n hn p q h i x

end FLT.Mazur.PolygonPinching

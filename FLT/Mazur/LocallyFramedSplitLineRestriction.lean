/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyFramedSplitLineProjective

/-!
# Affine test maps of the glued split-line point

The glued point recovers the point of any affine test map equipped with a
frame and splitting. The test map need not factor through a chosen chart:
comparison is checked on affine refinements of its inverse-image cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallyFramedSplitLineProjective
open FCurve ProjectiveSpace AffineSplitLineCoordinates
variable {X : Scheme.{u}} {ι : Type u} [Finite ι] {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι) (C : X.OpenCover.{v})
variable [∀ i, IsAffine (C.X i)]
variable (e : ∀ i, (pullback (C.f i)).obj L ≅ structureModule (C.X i))
variable (r : ∀ i, SheafOfModules.free ι ⟶ (pullback (C.f i)).obj L)
variable (hr : ∀ i, SplitSheafLinePullback.inclusion (C.f i) s ≫ r i = 𝟙 _)

/-- Restriction along any framed split affine test map recovers its intrinsic point. -/
lemma affine_test {T : Scheme.{u}} [IsAffine T] (f : T ⟶ X)
    (d : (pullback f).obj L ≅ structureModule T)
    (q : SheafOfModules.free ι ⟶ (pullback f).obj L)
    (hq : SplitSheafLinePullback.inclusion f s ≫ q = 𝟙 _) :
    f ≫ morphism s C e r hr =
      projectivePoint d (SplitSheafLinePullback.inclusion f s) q hq ≫
        coefficientMap f.appTop.hom ι := by
  let D : T.OpenCover := C.pullback₁ f
  apply D.hom_ext
  intro i
  apply ((C.pullback₁ f).X i).affineCover.hom_ext
  intro a
  let t := ((C.pullback₁ f).X i).affineCover.f a
  have h : (t ≫ (C.pullback₁ f).f i) ≫ f =
      (t ≫ C.pullbackHom f i) ≫ C.f i := by
    simp only [Category.assoc, C.pullbackHom_map]
  have hp := projectivePoint_common_refinement s
    (t ≫ (C.pullback₁ f).f i) (t ≫ C.pullbackHom f i) f (C.f i) h
    d (e i) q (r i) hq (hr i)
  calc
    t ≫ (C.pullback₁ f).f i ≫ f ≫ morphism s C e r hr =
        (t ≫ C.pullbackHom f i) ≫ C.f i ≫ morphism s C e r hr := by
      simp only [← Category.assoc]
      rw [h]
    _ = (t ≫ C.pullbackHom f i) ≫ localPoint s C e r hr i := by
      rw [ι_morphism]
    _ = t ≫ (C.pullback₁ f).f i ≫
        (projectivePoint d (SplitSheafLinePullback.inclusion f s) q hq ≫
          coefficientMap f.appTop.hom ι) := by
      exact hp.symm.trans (Category.assoc _ _ _)

end FLT.Mazur.LocallyFramedSplitLineProjective

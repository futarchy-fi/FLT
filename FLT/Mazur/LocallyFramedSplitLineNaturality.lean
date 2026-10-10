/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyFramedSplitLineRestriction

/-!
# Naturality of the glued locally framed split-line point

Arbitrary geometric pullback of the original inclusion agrees with pullback
of its projective point. The two affine covers and their frames and splittings
are independent; the comparison on each affine test map uses the genuine
pullback composition isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallyFramedSplitLineProjective
open FCurve ProjectiveSpace AffineSplitLineCoordinates
variable {X Y : Scheme.{u}} {ι : Type u} [Finite ι] {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι) (C : X.OpenCover.{v})
variable [∀ i, IsAffine (C.X i)]
variable (e : ∀ i, (pullback (C.f i)).obj L ≅ structureModule (C.X i))
variable (r : ∀ i, SheafOfModules.free ι ⟶ (pullback (C.f i)).obj L)
variable (hr : ∀ i, SplitSheafLinePullback.inclusion (C.f i) s ≫ r i = 𝟙 _)

/-- The actual reverse projective construction commutes with arbitrary geometric pullback. -/
lemma morphism_pullback (f : Y ⟶ X) (D : Y.OpenCover.{w}) [∀ i, IsAffine (D.X i)]
    (d : ∀ i, (pullback (D.f i)).obj ((pullback f).obj L) ≅ structureModule (D.X i))
    (q : ∀ i, SheafOfModules.free ι ⟶ (pullback (D.f i)).obj ((pullback f).obj L))
    (hq : ∀ i, SplitSheafLinePullback.inclusion (D.f i)
      (SplitSheafLinePullback.inclusion f s) ≫ q i = 𝟙 _) :
    f ≫ morphism s C e r hr =
      morphism (SplitSheafLinePullback.inclusion f s) D d q hq ≫
        coefficientMap f.appTop.hom ι := by
  apply D.hom_ext
  intro i
  let a := (pullbackComp (D.f i) f).app L
  have hi : a.hom ≫ SplitSheafLinePullback.inclusion (D.f i ≫ f) s =
      SplitSheafLinePullback.inclusion (D.f i)
        (SplitSheafLinePullback.inclusion f s) :=
    SplitSheafLinePullback.inclusion_comp (D.f i) f s
  let c := a.symm ≪≫ d i
  let t := q i ≫ a.hom
  have ht : SplitSheafLinePullback.inclusion (D.f i ≫ f) s ≫ t = 𝟙 _ := by
    apply (cancel_epi a.hom).mp
    change a.hom ≫ (SplitSheafLinePullback.inclusion (D.f i ≫ f) s ≫
      (q i ≫ a.hom)) = a.hom ≫ 𝟙 _
    rw [← Category.assoc, hi,
      ← Category.assoc, hq i]
    exact (Category.id_comp a.hom).trans (Category.comp_id a.hom).symm
  have hp := projectivePoint_sourceIso a (d i) c
    (SplitSheafLinePullback.inclusion (D.f i) (SplitSheafLinePullback.inclusion f s))
    (SplitSheafLinePullback.inclusion (D.f i ≫ f) s) (q i) t (hq i) ht
    (SplitSheafLinePullback.inclusion_comp (D.f i) f s)
  rw [← Category.assoc, affine_test s C e r hr (D.f i ≫ f) c t ht,
    ι_morphism_assoc]
  unfold localPoint
  rw [hp, Category.assoc, coefficientMap_appTop_comp]

end FLT.Mazur.LocallyFramedSplitLineProjective

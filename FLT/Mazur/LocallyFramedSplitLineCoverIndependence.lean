/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyFramedSplitLineRestriction

/-!
# Independence of the affine framed split cover

The affine test-map law identifies points constructed from different covers,
with independently chosen frames and retractions and no refinement supplied.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallyFramedSplitLineProjective
open FCurve
variable {X : Scheme.{u}} {ι : Type u} [Finite ι] {L : X.Modules}
variable (s : L ⟶ SheafOfModules.free ι) (C : X.OpenCover.{v})
variable [∀ i, IsAffine (C.X i)]
variable (e : ∀ i, (pullback (C.f i)).obj L ≅ structureModule (C.X i))
variable (r : ∀ i, SheafOfModules.free ι ⟶ (pullback (C.f i)).obj L)
variable (hr : ∀ i, SplitSheafLinePullback.inclusion (C.f i) s ≫ r i = 𝟙 _)

/-- Any two affine framed split covers construct the same projective morphism. -/
lemma morphism_cover_independent (D : X.OpenCover.{w}) [∀ i, IsAffine (D.X i)]
    (d : ∀ i, (pullback (D.f i)).obj L ≅ structureModule (D.X i))
    (q : ∀ i, SheafOfModules.free ι ⟶ (pullback (D.f i)).obj L)
    (hq : ∀ i, SplitSheafLinePullback.inclusion (D.f i) s ≫ q i = 𝟙 _) :
    morphism s C e r hr = morphism s D d q hq := by
  apply D.hom_ext
  intro i
  rw [ι_morphism]
  exact affine_test s C e r hr (D.f i) (d i) (q i) (hq i)

end FLT.Mazur.LocallyFramedSplitLineProjective

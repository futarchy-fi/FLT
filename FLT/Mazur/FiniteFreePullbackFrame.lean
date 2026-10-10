/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeSheafRestrictionCoherence
public import FLT.Mazur.AffineFreeSheafCoordinatePullback

/-!
# Actual finite free frames under pullback

Pull back a sheaf frame through the canonical free-sheaf comparison. Changes
between two such frames are the actual pullbacks of their coordinate changes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreePullbackFrame
open ModuleGlobalEvaluationPullback AffineFreeSheafCoordinates
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The genuine pullback of a finite free sheaf frame. -/
def frame {M : Y.Modules} {ι : Type u} (e : M ≅ SheafOfModules.free ι) :
    (pullback f).obj M ≅ SheafOfModules.free ι :=
  (pullback f).mapIso e ≪≫ freeIso f ι

/-- Changes of pulled frames are the pulled changes of the original frames. -/
lemma change_frame {M : Y.Modules} {ι κ : Type u}
    (e : M ≅ SheafOfModules.free ι) (d : M ≅ SheafOfModules.free κ) :
    (frame f e).symm ≪≫ frame f d = pullbackFreeIso f (e.symm ≪≫ d) := by
  apply Iso.ext
  simp [frame, pullbackFreeIso]

/-- Two successive pulled frames agree through the actual composition comparison. -/
lemma frame_comp {M : Z.Modules} {ι : Type u} (e : M ≅ SheafOfModules.free ι) :
    (pullbackComp f g).app M ≪≫ frame (f ≫ g) e = frame f (frame g e) := by
  apply Iso.ext
  apply (cancel_epi ((pullbackComp f g).inv.app M)).mp
  simp only [Iso.trans_hom, Iso.app_hom, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]
  dsimp only [frame, Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (pullbackComp f g).inv.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  change (pullback (f ≫ g)).map e.hom ≫ (freeIso (f ≫ g) ι).hom =
    (pullback (f ≫ g)).map e.hom ≫ (pullbackComp f g).inv.app _ ≫
      (pullback f).map (freeIso g ι).hom ≫ (freeIso f ι).hom
  rw [freeIso_comp]

/-- A commuting geometric triangle retains the same actual pulled frame. -/
lemma frame_congr {k : X ⟶ Z} (h : f ≫ g = k) {M : Z.Modules} {ι : Type u}
    (e : M ≅ SheafOfModules.free ι) :
    (pullbackComp f g).app M ≪≫ (pullbackCongr h).app M ≪≫ frame k e =
      frame f (frame g e) := by
  subst k
  apply Iso.ext
  simpa [pullbackCongr] using congrArg Iso.hom (frame_comp f g e)

end FLT.Mazur.FiniteFreePullbackFrame

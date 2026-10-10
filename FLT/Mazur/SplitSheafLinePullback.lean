/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalEvaluationPullback

/-!
# Pulling back actual split sheaf inclusions

Use the canonical scalar and free-sheaf comparisons to pull back a frame,
inclusion and retraction. The original splitting and frame section survive
arbitrary geometric pullback, including open restriction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitSheafLinePullback
open FCurve
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules} {ι : Type u}

/-- Pull back the original frame through the canonical scalar comparison. -/
def frame (e : L ≅ structureModule Y) : (pullback f).obj L ≅ structureModule X :=
  (pullback f).mapIso e ≪≫ modulePullbackUnitIso f

/-- Pull back the original inclusion into the canonical free sheaf. -/
def inclusion (s : L ⟶ SheafOfModules.free ι) :
    (pullback f).obj L ⟶ SheafOfModules.free ι :=
  (pullback f).map s ≫ (ModuleGlobalEvaluationPullback.freeIso f ι).hom

/-- Pull back the original retraction using the inverse free comparison. -/
def retraction (r : SheafOfModules.free ι ⟶ L) :
    SheafOfModules.free ι ⟶ (pullback f).obj L :=
  (ModuleGlobalEvaluationPullback.freeIso f ι).inv ≫ (pullback f).map r

/-- The actual original splitting proves the pulled-back splitting. -/
lemma inclusion_retraction (s : L ⟶ SheafOfModules.free ι)
    (r : SheafOfModules.free ι ⟶ L) (hs : s ≫ r = 𝟙 L) :
    inclusion f s ≫ retraction f r = 𝟙 ((pullback f).obj L) := by
  simp only [inclusion, retraction, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp, hs]
  exact (pullback f).map_id L

/-- The pulled frame at one is the actual pullback of the original frame section. -/
lemma frame_section (e : L ≅ structureModule Y) :
    (frame f e).inv.app ⊤ (1 : Γ(X, ⊤)) =
      pullGlobal f L (e.inv.app ⊤ (1 : Γ(Y, ⊤))) :=
  (pullGlobal_hom f e.inv).symm

/-- The pulled inclusion applied to its frame is the original section pulled back. -/
lemma inclusion_frame_section (e : L ≅ structureModule Y)
    (s : L ⟶ SheafOfModules.free ι) :
    (inclusion f s).app ⊤ ((frame f e).inv.app ⊤ (1 : Γ(X, ⊤))) =
      (ModuleGlobalEvaluationPullback.freeIso f ι).hom.app ⊤
        (pullGlobal f _ (s.app ⊤ (e.inv.app ⊤ (1 : Γ(Y, ⊤))))) := by
  rw [frame_section]
  change (ModuleGlobalEvaluationPullback.freeIso f ι).hom.app ⊤
    (((pullback f).map s).app ⊤ (pullGlobal f L _)) = _
  rw [pullGlobal_naturality]

end FLT.Mazur.SplitSheafLinePullback

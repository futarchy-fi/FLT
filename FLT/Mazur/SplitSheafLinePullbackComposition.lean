/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitSheafLinePullback
public import FLT.Mazur.FreeSheafRestrictionCoherence

/-!
# Coherence of pulled split-line inclusions

The genuine pullback composition isomorphism respects the inclusion into
the canonical free sheaf. This supplies the ambient square on common
affine refinements without adding a compatibility assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitSheafLinePullback
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable {L : Z.Modules} {ι : Type u} (s : L ⟶ SheafOfModules.free ι)

/-- The actual composition comparison commutes with the original ambient inclusion. -/
lemma inclusion_comp :
    (pullbackComp f g).hom.app L ≫ inclusion (f ≫ g) s =
      inclusion f (inclusion g s) := by
  apply (cancel_epi ((pullbackComp f g).inv.app L)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  unfold inclusion
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn := (pullbackComp f g).inv.naturality s
  dsimp only [Functor.comp_map] at hn
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  change (pullback (f ≫ g)).map s ≫
    (ModuleGlobalEvaluationPullback.freeIso (f ≫ g) ι).hom =
      (pullback (f ≫ g)).map s ≫ (pullbackComp f g).inv.app _ ≫
        (pullback f).map (ModuleGlobalEvaluationPullback.freeIso g ι).hom ≫
          (ModuleGlobalEvaluationPullback.freeIso f ι).hom
  rw [ModuleGlobalEvaluationPullback.freeIso_comp]

/-- Equality of geometric maps preserves their original pulled inclusion. -/
lemma inclusion_congr {k : X ⟶ Z} (h : f ≫ g = k) :
    ((pullbackComp f g).app L ≪≫ (pullbackCongr h).app L).hom ≫ inclusion k s =
      inclusion f (inclusion g s) := by
  subst k
  simpa [pullbackCongr] using inclusion_comp f g s


/-- A local source frame constructs a frame on the original composite pullback. -/
def frameOver {k : X ⟶ Z} (h : f ≫ g = k)
    (e : (pullback g).obj L ≅ FCurve.structureModule Y) :
    (pullback k).obj L ≅ FCurve.structureModule X :=
  ((pullbackComp f g).app L ≪≫ (pullbackCongr h).app L).symm ≪≫ frame f e

/-- The local retraction constructs a retraction on that same composite pullback. -/
def retractionOver {k : X ⟶ Z} (h : f ≫ g = k)
    (r : SheafOfModules.free ι ⟶ (pullback g).obj L) :
    SheafOfModules.free ι ⟶ (pullback k).obj L :=
  retraction f r ≫ ((pullbackComp f g).app L ≪≫ (pullbackCongr h).app L).hom

/-- The constructed composite retraction really splits the original pulled inclusion. -/
lemma inclusion_retractionOver {k : X ⟶ Z} (h : f ≫ g = k)
    (r : SheafOfModules.free ι ⟶ (pullback g).obj L)
    (hr : inclusion g s ≫ r = 𝟙 _) :
    inclusion k s ≫ retractionOver f g h r = 𝟙 _ := by
  let a := (pullbackComp f g).app L ≪≫ (pullbackCongr h).app L
  apply (cancel_epi a.hom).mp
  change a.hom ≫ (inclusion k s ≫ (retraction f r ≫ a.hom)) = a.hom ≫ 𝟙 _
  rw [← Category.assoc, inclusion_congr f g s h, ← Category.assoc,
    inclusion_retraction f _ r hr]
  exact (Category.id_comp a.hom).trans (Category.comp_id a.hom).symm

end FLT.Mazur.SplitSheafLinePullback

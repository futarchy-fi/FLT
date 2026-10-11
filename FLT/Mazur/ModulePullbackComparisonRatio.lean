/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackStageIso

/-!
# Comparing two coherent original-stage identifications

Two complete lines compared with the same original stage line determine
compatible stage isomorphisms between their actual pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p) {L M : S.Modules} {A : X.Modules} {B : Y.Modules}

/-- Ratios of two coherent stage comparisons give a commuting original-stage square. -/
theorem pullbackComparison_ratio
    (la : (pullback p).obj L ≅ A) (lb : (pullback q).obj L ≅ B)
    (ma : (pullback p).obj M ≅ A) (mb : (pullback q).obj M ≅ B)
    (d : (pullback r).obj B ⟶ A)
    (hl : (pullback r).map lb.hom ≫ d = (pullbackStageIso p q r h L).hom ≫ la.hom)
    (hm : (pullback r).map mb.hom ≫ d = (pullbackStageIso p q r h M).hom ≫ ma.hom) :
    (pullback r).map (lb ≪≫ mb.symm).hom ≫ (pullbackStageIso p q r h M).hom =
      (pullbackStageIso p q r h L).hom ≫ (la ≪≫ ma.symm).hom := by
  apply (cancel_mono ma.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← hm, Iso.map_inv_hom_id_assoc, hl]

end FLT.Mazur.FCurve

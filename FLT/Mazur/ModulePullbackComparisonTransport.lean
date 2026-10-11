/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackStageIso

/-!
# Transporting coherent stage comparisons through module isomorphisms

The original stage comparison respects the tensor pullback and structure-module
comparisons, including the given equality of the composite scheme map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p)

/-- The sealed comparison is natural in the complete module. -/
theorem pullbackStageIso_naturality {L L' : S.Modules} (e : L ⟶ L') :
    (pullback r).map ((pullback q).map e) ≫ (pullbackStageIso p q r h L').hom =
      (pullbackStageIso p q r h L).hom ≫ (pullback p).map e := by
  simpa only [pullbackStageIso_hom, NatTrans.comp_app, Functor.comp_map] using
    ((pullbackComp r q).hom ≫ (pullbackCongr h).hom).naturality e

/-- Changing the complete and stage modules by actual isomorphisms preserves coherence. -/
theorem pullbackComparison_transport
    {L L' : S.Modules} {M M' : Y.Modules} {N N' : X.Modules}
    (l : L' ≅ L) (m : M' ≅ M) (n : N' ≅ N)
    (a : (pullback q).obj L ≅ M) (b : (pullback r).obj M ≅ N)
    (c : (pullback p).obj L ≅ N)
    (hc : (pullback r).map a.hom ≫ b.hom = (pullbackStageIso p q r h L).hom ≫ c.hom) :
    (pullback r).map (((pullback q).mapIso l ≪≫ a ≪≫ m.symm).hom) ≫
        ((pullback r).mapIso m ≪≫ b ≪≫ n.symm).hom =
      (pullbackStageIso p q r h L').hom ≫
        ((pullback p).mapIso l ≪≫ c ≪≫ n.symm).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [← Category.assoc _ b.hom, hc, Category.assoc,
    ← Category.assoc _ (pullbackStageIso p q r h L).hom,
    pullbackStageIso_naturality, Category.assoc]

end FLT.Mazur.FCurve

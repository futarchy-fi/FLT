/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeRefinementPullback

/-!
# Ambient sheaf changes on refined finite free charts

Refining coordinates commutes with an isomorphism of the original ambient
sheaves. The resulting coordinate square includes the actual pullback map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open AffineFreeSheafCoordinates
variable {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N)

/-- Restricting a transported frame is transport of the restricted frame. -/
lemma refineChart_ambient {U V : X.Opens} (h : U ≤ V) {ι : Type u}
    (e : N.restrict V.ι ≅ SheafOfModules.free ι) :
    refineChart M h ((restrictFunctor V.ι).mapIso a ≪≫ e) =
      (restrictFunctor U.ι).mapIso a ≪≫ refineChart N h e := by
  apply Iso.ext
  simp only [refineChart, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Iso.app_hom, Category.assoc]
  have hc := (restrictFunctorComp (X.homOfLE h) V.ι).hom.naturality a.hom
  have hg := (restrictFunctorCongr (X.homOfLE_ι h).symm).hom.naturality a.hom
  dsimp only [Functor.comp_map] at hc
  rw [reassoc_of% hg, reassoc_of% hc]

/-- The coordinate change of an ambient isomorphism on a chosen open. -/
def ambientChange {U : X.Opens} {ι κ : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : N.restrict U.ι ≅ SheafOfModules.free κ) :
    (SheafOfModules.free ι : U.toScheme.Modules) ≅ SheafOfModules.free κ :=
  e.symm ≪≫ (restrictFunctor U.ι).mapIso a ≪≫ d

/-- The original ambient coordinate changes commute with actual chart refinement. -/
lemma ambientChange_refinement {U V : X.Opens} (h : U ≤ V)
    {ι κ ν ξ : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ)
    (c : N.restrict U.ι ≅ SheafOfModules.free ν)
    (b : N.restrict V.ι ≅ SheafOfModules.free ξ) :
    transition M le_rfl h e d ≪≫
        pullbackFreeIso (X.homOfLE h) (ambientChange a d b) =
      ambientChange a e c ≪≫ transition N le_rfl h c b := by
  rw [transition, transition, refineChart_self, refineChart_self]
  have hr := refineChart_change M h d ((restrictFunctor V.ι).mapIso a ≪≫ b)
  rw [refineChart_ambient] at hr
  change e.symm ≪≫ refineChart M h d ≪≫
      pullbackFreeIso (X.homOfLE h) (ambientChange a d b) = _
  dsimp only [ambientChange]
  rw [← hr]
  apply Iso.ext
  simp

end FLT.Mazur.FiniteFreeChartTransitions

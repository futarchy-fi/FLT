/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitLineChartRefinement
public import FLT.Mazur.LocallySplitLineAmbientTransport

/-!
# Actual reverse points commute with dual projective chart inclusions

Ambient isomorphism transport and ordinary open restriction identify the
reverse points on varying finite free charts, with no supplied compatibility
condition. In particular they form a compatible family for the glued atlas.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallySplitLineAmbientChart
open FCurve SplitLineAffineNeighborhood ProjectiveSpace FiniteFreeChartTransitions
open AffineFreeSheafCoordinates FiniteFreeContragredient SplitLineAffinePresentation
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)

/-- Two actual free frames on one affine ambient chart give dual-transported reverse points. -/
lemma point_chartIso (U : X.Opens) [IsAffine U.toScheme]
    {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict U.ι ≅ SheafOfModules.free κ) :
    point s hL hs U e ≫ (linearIso (map (coordinates U.toScheme (e.symm ≪≫ d)))).hom =
      point s hL hs U d := by
  have hp := morphism_ambientIso (inclusion s U e) (hL.restrict U.ι)
    (inclusion_locallySplit s hs U e) (e.symm ≪≫ d)
  exact hp.trans (by
    unfold point
    congr 1
    simp only [inclusion, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc])

/-- Refining a chart to the same base open leaves its original reverse point unchanged. -/
lemma point_refine_self (U : X.Opens) {ι : Type u} [Finite ι]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι) :
    point s hL hs U (refineChart M le_rfl e) = point s hL hs U e := by
  have hp := point_refinement s (show U ≤ U from le_rfl) e hL hs
  have hf : X.homOfLE (show U ≤ U from le_rfl) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    simp
  rw [hf, coefficientMap_appTop_id, Category.id_comp, Category.comp_id] at hp
  exact hp.symm

/-- The reverse points of two refined ambient charts satisfy their actual dual transition. -/
lemma point_dualTransition {U V W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ U) (hV : W ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    point s hL hs W (refineChart M hU e) ≫
        (dualProjectiveTransition M hU hV e d).hom =
      point s hL hs W (refineChart M hV d) :=
  point_chartIso s hL hs W (refineChart M hU e) (refineChart M hV d)

/-- Actual atlas refinement compatibility, including the genuine coefficient map. -/
lemma point_dualChartInclusion {U V : X.Opens} [IsAffine U.toScheme]
    (h : U ≤ V) {ι κ : Type u} [Finite ι] [Finite κ]
    (e : M.restrict U.ι ≅ SheafOfModules.free ι)
    (d : M.restrict V.ι ≅ SheafOfModules.free κ) :
    point s hL hs U e ≫ dualChartInclusion M h e d =
      X.homOfLE h ≫ point s hL hs V d := by
  rw [dualChartInclusion, ← Category.assoc,
    ← point_refine_self s hL hs U e, point_dualTransition]
  exact (point_refinement s h d hL hs).symm

end FLT.Mazur.LocallySplitLineAmbientChart

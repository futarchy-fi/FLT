/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatCartierIdealPullback
public import FLT.Mazur.IdealModulePullbackCoherence
public import FLT.Mazur.SchemeOverlapDiagonalChart

/-!
# Canonical line isomorphisms from equality of full Cartier ideals

Equal pulled-back ideals identify their actual ideal line bundles through
canonical inclusion-preserving comparisons. Normalizing these isomorphisms
along any test map preserves the pulled-back inclusion as well.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open SheafPullbackPathComparison SchemeOverlapDiagonalChart
variable {X Y T : Scheme.{u}} (I : Y.IdealSheafData)

/-- An equality of full ideal comaps gives the canonical ideal-line overlap isomorphism. -/
def cartierIdealOverlapIso (l r : X ⟶ Y)
    (h : I.comap l = I.comap r)
    [IsIso (idealModulePullbackHom I l)] [IsIso (idealModulePullbackHom I r)] :
    (pullback l).obj (idealModule I) ≅ (pullback r).obj (idealModule I) :=
  idealModulePullbackIsoOfEq I l (I.comap r) h ≪≫ (asIso (idealModulePullbackHom I r)).symm

/-- The actual full-ideal comparison preserves the inclusion into the structure sheaf. -/
lemma cartierIdealOverlapIso_inclusion (l r : X ⟶ Y)
    (h : I.comap l = I.comap r)
    [IsIso (idealModulePullbackHom I l)] [IsIso (idealModulePullbackHom I r)] :
    (cartierIdealOverlapIso I l r h).hom ≫ idealModulePullbackι I r =
      idealModulePullbackι I l := by
  rw [← idealModulePullbackHom_ι I r]
  simp only [cartierIdealOverlapIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id_assoc]
  exact idealModulePullbackIsoOfEq_ι I l (I.comap r) h

/-- Normalized transport of any inclusion-preserving overlap still preserves the inclusion. -/
lemma idealOverlap_normalize_inclusion (l r : X ⟶ Y) (t : T ⟶ X) (a b : T ⟶ Y)
    (ha : t ≫ l = a) (hb : t ≫ r = b)
    (e : (pullback l).obj (idealModule I) ≅ (pullback r).obj (idealModule I))
    (he : e.hom ≫ idealModulePullbackι I r = idealModulePullbackι I l) :
    (normalize l r t a b ha hb (idealModule I) e).hom ≫ idealModulePullbackι I b =
      idealModulePullbackι I a := by
  apply (cancel_epi ((comparison t l a ha).hom.app (idealModule I))).mp
  dsimp only [SchemeOverlapDiagonalChart.normalize, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← idealModulePullbackι_comparison I t r b hb, ← Functor.map_comp_assoc, he]
  exact idealModulePullbackι_comparison I t l a ha

/-- Cartier pullback makes the pulled-back full-ideal inclusion a monomorphism. -/
theorem idealModulePullbackι_mono (f : X ⟶ Y)
    [IsIso (idealModulePullbackHom I f)] : Mono (idealModulePullbackι I f) := by
  rw [← idealModulePullbackHom_ι]
  infer_instance

end FLT.Mazur.FCurve

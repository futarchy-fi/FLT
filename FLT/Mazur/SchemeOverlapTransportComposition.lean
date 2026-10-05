/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapDiagonalChart

/-!
# Composing normalized overlap transports

Normalizing an overlap successively along two scheme maps agrees with
normalizing along their composite. This supplies the sheaf comparison
needed to transport cocycle equations between overlap charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapDiagonalChart
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z Z' T : Scheme.{u}}

/-- Successive normalized overlap pullbacks equal the normalization along the composite. -/
theorem normalize_comp (l r : Z ⟶ Y) (k : Z' ⟶ Z) (l' r' : Z' ⟶ Y)
    (wl : k ≫ l = l') (wr : k ≫ r = r') (t : T ⟶ Z') (l'' r'' : T ⟶ Y)
    (vl : t ≫ l' = l'') (vr : t ≫ r' = r'')
    (ul : (t ≫ k) ≫ l = l'') (ur : (t ≫ k) ≫ r = r'')
    (M : Y.Modules) (e : (pullback l).obj M ≅ (pullback r).obj M) :
    normalize l' r' t l'' r'' vl vr M (normalize l r k l' r' wl wr M e) =
      normalize l r (t ≫ k) l'' r'' ul ur M e := by
  have hl := comparison_assoc t k l (t ≫ k) l' l'' rfl wl vl ul M
  have hr := comparison_assoc t k r (t ≫ k) r' r'' rfl wr vr ur M
  have hn := (comparison t k (t ≫ k) rfl).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  apply Iso.ext
  apply (cancel_epi ((comparison t l' l'' vl).hom.app M)).mp
  dsimp only [normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom]
  simp only [Iso.hom_inv_id_app_assoc]
  apply (cancel_epi ((pullback t).map ((comparison k l l' wl).hom.app M))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hr, ← Category.assoc ((pullback t).map ((pullback k).map e.hom)), hn]
  simp only [Category.assoc]
  rw [← Category.assoc ((pullback t).map ((comparison k l l' wl).hom.app M)), hl]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Successive transport can be normalized to any equal composite scheme map. -/
theorem normalize_comp_of_eq (l r : Z ⟶ Y) (k : Z' ⟶ Z) (l' r' : Z' ⟶ Y)
    (wl : k ≫ l = l') (wr : k ≫ r = r') (t : T ⟶ Z') (s : T ⟶ Z)
    (ws : t ≫ k = s) (l'' r'' : T ⟶ Y)
    (vl : t ≫ l' = l'') (vr : t ≫ r' = r'')
    (ul : s ≫ l = l'') (ur : s ≫ r = r'')
    (M : Y.Modules) (e : (pullback l).obj M ≅ (pullback r).obj M) :
    normalize l' r' t l'' r'' vl vr M (normalize l r k l' r' wl wr M e) =
      normalize l r s l'' r'' ul ur M e := by
  subst s
  exact normalize_comp l r k l' r' wl wr t l'' r'' vl vr ul ur M e

end FLT.Mazur.SchemeOverlapDiagonalChart

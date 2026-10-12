/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackAmbientNormalization

/-!
# Sealed ambient comparison squares

The literal ambient square is packaged before specialization to tensor
sheaves. Its projection consumer retains any full original quotient map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackAmbientMatch
universe u v
section Category
variable {C D E : Type*} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (n : F ⋙ G ≅ H)
  {V : C} {S : D} {K : E} (a : F.obj V ≅ S) (c : G.obj S ≅ K) (e : H.obj V ≅ K)

/-- The literal commutative square relating global and coordinate ambient comparisons. -/
@[irreducible] def Matches : Prop :=
  G.map a.hom ≫ c.hom = n.hom.app V ≫ e.hom

/-- The sealed square implies equality of the full original normalized quotient maps. -/
theorem projection (h : Matches F G H n a c e) {Q : C} (q : V ⟶ Q) :
    c.inv ≫ G.map (a.inv ≫ F.map q) = (e.inv ≫ H.map q) ≫ n.inv.app Q := by
  unfold Matches at h
  apply (cancel_epi c.hom).mp
  apply (cancel_epi (G.map a.hom)).mp
  simp only [Iso.hom_inv_id_assoc, Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.hom_inv_id]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (n.hom.app V), ← n.hom.naturality q]
  simp only [Functor.comp_map, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    G.map_id, Category.id_comp]

/-- Access the original ambient square without expanding any concrete tensor construction. -/
theorem equation (h : Matches F G H n a c e) :
    G.map a.hom ≫ c.hom = n.hom.app V ≫ e.hom := by
  unfold Matches at h
  exact h
end Category

open SheafPullbackPathComparison SheafPullbackAmbientNormalization
variable {S T X Y : Scheme.{u}}
variable (z : T ⟶ X) (p : X ⟶ Y) (s : Y ⟶ S) (β : X ⟶ S)
  (g : T ⟶ Y) (t : T ⟶ S)
  (hp : p ≫ s = β) (hg : z ≫ p = g) (ht : z ≫ β = t) (hgt : g ≫ s = t)
variable (L : S.Modules) (V : Y.Modules) (K : T.Modules)
  (a : (pullback s).obj L ≅ V) (c : (pullback t).obj L ≅ K)
  (e : (pullback g).obj V ≅ K)
attribute [local irreducible] Scheme.Modules.pullback comparison

/-- Coherent coefficient comparisons construct the sealed actual ambient square. -/
theorem chart_matches
    (hc : e.inv ≫ (pullback g).map a.inv ≫ (comparison g s t hgt).hom.app L = c.inv) :
    Matches (pullback p) (pullback z) (pullback g) (comparison z p g hg)
      (chartIso p s β hp L V a) (testIso z β t ht L K c) e := by
  unfold Matches
  exact chartIso_test z p s β g t hp hg ht hgt L V K a c e hc

end FLT.Mazur.SheafPullbackAmbientMatch

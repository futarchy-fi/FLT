/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackCompositeCharts
public import FLT.Mazur.RigidifiedPicardPullback

/-!
# Normalizing local section frames around two squares

A frame on a restricted total-space line gives a base frame through the
section square. Its further normalized restriction retains both comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison FCurve FCurve.LineSheafSectionRigidity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z S T U : Scheme.{u}}
variable (s : S ⟶ X) (t : T ⟶ Y) (r : U ⟶ Z)
variable (p : Y ⟶ X) (b : T ⟶ S) (q : Z ⟶ Y) (c : U ⟶ T)
variable (w : t ≫ p = b ≫ s) (v : r ≫ q = c ≫ t)
variable (qp : Z ⟶ X) (cb : U ⟶ S) (hp : q ≫ p = qp) (hb : c ≫ b = cb)
variable (wv : r ≫ qp = cb ≫ s)

/-- Normalization of a transported rigidification is normalization of its base frame. -/
theorem sectionFrame_normalize (A : X.Modules)
    (ρ : (pullback t).obj ((pullback p).obj A) ≅ structureModule T) :
    (pullback r).map ((comparison q p qp hp).inv.app A) ≫
        (squareIso t r q c v).hom.app ((pullback p).obj A) ≫
        (pullback c).map ρ.hom ≫ (modulePullbackUnitIso c).hom =
      (squareIso s r qp cb wv).hom.app A ≫
        (comparison c b cb hb).inv.app ((pullback s).obj A) ≫
        (pullback c).map ((squareIso s t p b w).inv.app A ≫ ρ.hom) ≫
        (modulePullbackUnitIso c).hom := by
  apply (cancel_epi ((pullback r).map ((comparison q p qp hp).hom.app A))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [squareIso_composite_charts_assoc s t r p b q c w v qp cb hp hb wv]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SchemePullbackSquare

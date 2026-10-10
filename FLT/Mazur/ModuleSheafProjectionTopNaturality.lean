/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafProjectionSections

/-!
# Restriction of projection sections on whole charts

A compatible pair of ambient projections gives an actual equation on chart
sections. The specified preimage equalities remain part of the comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafProjectionSections

/-- Composition of projections respects specified whole-chart coordinates. -/
lemma sections_comp_top {X Y Z : Scheme.{u}} (a : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z)
    (h : a ≫ i = j) (G : Z.Modules) (M : Y.Modules) (N : X.Modules)
    (q : G ⟶ (pushforward i).obj M) (t : M ⟶ (pushforward a).obj N)
    (W : Z.Opens) (hi : i ⁻¹ᵁ W = ⊤) (hj : j ⁻¹ᵁ W = ⊤) :
    sections j G N
        (q ≫ (pushforward i).map t ≫ (pushforwardComp a i).hom.app N ≫
          (pushforwardCongr h).hom.app N) W ⊤ hj =
      sections i G M q W ⊤ hi ≫ t.app ⊤ := by
  subst j
  ext s
  simp only [sections, Hom.comp_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, eqToHom_refl, op_id, ConcreteCategory.comp_apply]
  rw [N.presheaf.map_id]
  exact (congrArg (fun k ↦ k (q.app W s))
    (t.mapPresheaf.naturality (eqToHom hi.symm).op)).symm

/-- Equal top preimages make projection coordinates invariant under ambient restriction. -/
lemma sections_restrict_top {X Y : Scheme.{u}} (i : Y ⟶ X)
    (G : X.Modules) (M : Y.Modules) (q : G ⟶ (pushforward i).obj M)
    {W Z : X.Opens} (k : W ⟶ Z) (hW : i ⁻¹ᵁ W = ⊤) (hZ : i ⁻¹ᵁ Z = ⊤) :
    G.presheaf.map k.op ≫ sections i G M q W ⊤ hW =
      sections i G M q Z ⊤ hZ := by
  have hh := sections_naturality i G M q k hW hZ (𝟙 ⊤)
  rw [op_id, M.presheaf.map_id, Category.comp_id] at hh
  exact hh

/-- Compatible ambient projections restrict by the original whole-chart transition. -/
lemma sections_naturality_top {X Y Z : Scheme.{u}} (a : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z)
    (h : a ≫ i = j) (G : Z.Modules) (M : Y.Modules) (N : X.Modules)
    (q : G ⟶ (pushforward i).obj M) (r : G ⟶ (pushforward j).obj N)
    (t : M ⟶ (pushforward a).obj N)
    (ht : q ≫ (pushforward i).map t ≫ (pushforwardComp a i).hom.app N ≫
      (pushforwardCongr h).hom.app N = r)
    {W V : Z.Opens} (k : W ⟶ V) (hi : i ⁻¹ᵁ V = ⊤) (hj : j ⁻¹ᵁ W = ⊤) :
    G.presheaf.map k.op ≫ sections j G N r W ⊤ hj =
      sections i G M q V ⊤ hi ≫ t.app ⊤ := by
  have hjV : j ⁻¹ᵁ V = ⊤ := by
    apply top_unique
    rw [← hj]
    exact j.preimage_mono (leOfHom k)
  rw [sections_restrict_top j G N r k hj hjV, ← ht]
  exact sections_comp_top a i j h G M N q t V hi hjV

end FLT.Mazur.ModuleSheafProjectionSections

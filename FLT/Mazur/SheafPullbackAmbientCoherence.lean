/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIteratedPullbackSections
public import FLT.Mazur.SheafPullbackPathComparison
public import FLT.Mazur.QuotientRefinementCoherence

/-!
# Inverse ambient coherence in geometric path coordinates

Convert the ambient composition law on original sections to the inverse
path-comparison equation used to normalize global quotient projections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackAmbientCoherence
open SheafPullbackPathComparison AffineIteratedPullbackSections
universe u
variable {S T Y : Scheme.{u}} (g : T ⟶ Y) (s : Y ⟶ S) (t : T ⟶ S)
  (w : g ≫ s = t) (L : S.Modules)
attribute [local irreducible] Scheme.Modules.pullback

/-- The section-normalized composition is the canonical geometric path comparison. -/
theorem compositeIso_eq :
    compositeIso g s t w L = (SheafPullbackPathComparison.comparison g s t w).app L := by
  unfold compositeIso SheafPullbackPathComparison.comparison
  exact (NatIso.trans_app _ _ L).symm

attribute [local irreducible] compositeIso SheafPullbackPathComparison.comparison

/-- Original-section coherence gives the inverse geometric ambient equation. -/
theorem inverse_composite {V : Y.Modules} {K : T.Modules}
    (a : (pullback s).obj L ≅ V) (e : (pullback g).obj V ≅ K)
    (c : (pullback t).obj L ≅ K)
    (h : (compositeIso g s t w L).inv ≫ (pullback g).map a.hom ≫ e.hom = c.hom) :
    e.inv ≫ (pullback g).map a.inv ≫
      (SheafPullbackPathComparison.comparison g s t w).hom.app L = c.inv := by
  have hi := QuotientRefinementCoherence.inverse_triple (compositeIso g s t w L).symm
    ((pullback g).mapIso a) e c h
  rw [compositeIso_eq] at hi
  exact hi

end FLT.Mazur.SheafPullbackAmbientCoherence

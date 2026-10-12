/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackAmbientMatch
public import FLT.Mazur.SheafPullbackAmbientCoherence

/-!
# Ambient squares from original-section composition

Seal the forward section composition before applying inversion and geometric
normalization. This keeps concrete coefficient specializations small.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackAmbientSectionMatch
open SheafPullbackPathComparison SheafPullbackAmbientNormalization
universe u
variable {S T X Y : Scheme.{u}}
variable (g : T ⟶ Y) (s : Y ⟶ S) (t : T ⟶ S) (hgt : g ≫ s = t)
  (L : S.Modules) {V : Y.Modules} {K : T.Modules}
  (a : (pullback s).obj L ≅ V) (e : (pullback g).obj V ≅ K)
  (c : (pullback t).obj L ≅ K)
attribute [local irreducible] Scheme.Modules.pullback comparison
attribute [local irreducible] AffineIteratedPullbackSections.compositeIso

/-- The original-section composition equation before concrete coefficient substitution. -/
@[irreducible] def Composes : Prop :=
  (AffineIteratedPullbackSections.compositeIso g s t hgt L).inv ≫
    (pullback g).map a.hom ≫ e.hom = c.hom

/-- Original-section composition constructs the actual chart ambient square. -/
theorem toMatch (h : Composes g s t hgt L a e c)
    (z : T ⟶ X) (p : X ⟶ Y) (β : X ⟶ S)
    (hp : p ≫ s = β) (hg : z ≫ p = g) (ht : z ≫ β = t) :
    SheafPullbackAmbientMatch.Matches (pullback p) (pullback z) (pullback g)
      (comparison z p g hg) (chartIso p s β hp L V a) (testIso z β t ht L K c) e := by
  unfold Composes at h
  exact SheafPullbackAmbientMatch.chart_matches z p s β g t hp hg ht hgt L V K a c e
    (SheafPullbackAmbientCoherence.inverse_composite g s t hgt L a e c h)

end FLT.Mazur.SheafPullbackAmbientSectionMatch

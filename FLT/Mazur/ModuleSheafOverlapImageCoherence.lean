/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapCoordinateRefinement
public import FLT.Mazur.ModuleSheafLocalHomComposition

/-!
# Image-open coherence of chart transitions

Geometrically compatible chart comparisons induce the same transition on every
smaller image open. A chart cocycle therefore gives the actual section cocycle
needed to glue the chart pushforwards.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafOverlapImageTransition
open SheafPullbackPathComparison SheafPullbackMapNormalization
open ModuleSheafOpenImmersionLocalHom ModuleSheafMorphismGluing
universe u
variable {W O X Y Z : Scheme.{u}}
variable (i : Y ⟶ X) (j : Z ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
variable (p : O ⟶ Y) (q : O ⟶ Z) (r : O ⟶ X)
  (hi : p ≫ i = r) (hj : q ≫ j = r)
variable {M : Y.Modules} {N : Z.Modules}
variable (e : (pullback p).obj M ≅ (pullback q).obj N)
variable (t : W ⟶ O) (p' : W ⟶ Y) (q' : W ⟶ Z) (r' : W ⟶ X)
  (hp : t ≫ p = p') (hq : t ≫ q = q') (hr : t ≫ r = r')
  (hi' : p' ≫ i = r') (hj' : q' ≫ j = r')
variable (e' : (pullback p').obj M ≅ (pullback q').obj N)
variable (he : (pullback t).map e.hom ≫ (comparison t q q' hq).hom.app N =
  (comparison t p p' hp).hom.app M ≫ e'.hom)
attribute [local irreducible] Scheme.Modules.pullback comparison

include he in
/-- Actual coordinate refinement implies equality of normalized ambient transitions. -/
theorem ambientIso_normalize :
    normalize t r r r' r' hr hr (ambientIso i j p q r hi hj e).hom =
      (ambientIso i j p' q' r' hi' hj' e').hom := by
  have hn : normalize t p q p' q' hp hq e.hom = e'.hom := by
    apply (cancel_epi ((comparison t p p' hp).hom.app M)).mp
    rw [normalize_comm]
    exact he
  apply (cancel_mono (coordinateIso q' j r' hj' N).hom).mp
  rw [ambientIso_refine_coordinate t i j p q r hi hj p' q' r' hp hq hr hi' hj',
    hn, ambientIso_coordinate]

variable [IsOpenImmersion r] [IsOpenImmersion t] [IsOpenImmersion r']

include he hr in
/-- Geometric refinement restricts the same image transition on every smaller subopen. -/
theorem imageIso_refine_app (V : X.Opens) (hV : V ≤ r'.opensRange)
    (hVr : V ≤ r.opensRange) :
    localApp (imageIso i j p' q' r' hi' hj' e').hom hV =
      localApp (imageIso i j p q r hi hj e).hom hVr := by
  rw [imageIso_hom, imageIso_hom,
    ← ambientIso_normalize i j p q r hi hj e t p' q' r' hp hq hr hi' hj' e' he]
  exact localHom_normalize_app r t r' hr (ambientIso i j p q r hi hj e).hom V hV

section Cocycle
variable {Y' : Scheme.{u}} (k : Y' ⟶ X) [IsOpenImmersion k]
  (s : O ⟶ Y') (hk : s ≫ k = r) {P : Y'.Modules}
  (f : (pullback q).obj N ≅ (pullback s).obj P)
  (g : (pullback p).obj M ≅ (pullback s).obj P)
  (hc : e.hom ≫ f.hom = g.hom)

omit [IsOpenImmersion r] in
include hc in
/-- Conjugating chart transitions preserves their actual cocycle on a common scheme. -/
theorem ambientIso_cocycle :
    (ambientIso i j p q r hi hj e).hom ≫ (ambientIso j k q s r hj hk f).hom =
      (ambientIso i k p s r hi hk g).hom := by
  apply (cancel_mono (coordinateIso s k r hk P).hom).mp
  rw [Category.assoc, ambientIso_coordinate, ← Category.assoc,
    ambientIso_coordinate, Category.assoc, hc, ambientIso_coordinate]

include hc in
/-- The common-scheme cocycle holds on every subopen of its image. -/
theorem imageIso_cocycle_app (V : X.Opens) (hV : V ≤ r.opensRange)
    (a : Γ((pushforward i).obj M, V)) :
    localApp (imageIso j k q s r hj hk f).hom hV
        (localApp (imageIso i j p q r hi hj e).hom hV a) =
      localApp (imageIso i k p s r hi hk g).hom hV a := by
  exact localHom_cocycle_app r _ _ _
    (ambientIso_cocycle i j p q r hi hj e k s hk f g hc) V hV a

end Cocycle
end FLT.Mazur.ModuleSheafOverlapImageTransition

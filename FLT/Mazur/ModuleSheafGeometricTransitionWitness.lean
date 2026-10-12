/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGeometricOpenCocycle

/-!
# Indexed witnesses for geometric chart descent

Chart isomorphisms on all common subopens, with their proved pullback coherence
and cocycle, give the actual section cocycle for the original chart pushforwards.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafGluing
open ModuleSheafOpenImageChart ModuleSheafOpenOverlapTransition
open ModuleSheafMorphismGluing SheafPullbackPathComparison
universe u
attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.pushforward
variable {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u})
  (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)] (M : ∀ j, (Y j).Modules)
/-- A transition family is certified by geometric comparisons and their proved laws. -/
inductive GeometricTransitionWitness :
    (∀ j k, ((pushforward (i j)).obj (M j)).over
      ((i j).opensRange ⊓ (i k).opensRange) ≅
        ((pushforward (i k)).obj (M k)).over
          ((i j).opensRange ⊓ (i k).opensRange)) → Prop where
  /-- The witness uses the original geometric transitions without altering their maps. -/
  | ofGeometric
      (e : ∀ j k (U : X.Opens) (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange),
        (pullback (coordinate (i j) U hj)).obj (M j) ≅
          (pullback (coordinate (i k) U hk)).obj (M k))
      (hr : ∀ j k (U V : X.Opens) (h : V ≤ U)
        (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange),
        (pullback (X.homOfLE h)).map (e j k U hj hk).hom ≫
            (comparison (X.homOfLE h) (coordinate (i k) U hk)
              (coordinate (i k) V (h.trans hk)) (coordinate_refine (i k) h hk)).hom.app
                (M k) =
          (comparison (X.homOfLE h) (coordinate (i j) U hj)
              (coordinate (i j) V (h.trans hj)) (coordinate_refine (i j) h hj)).hom.app
                (M j) ≫ (e j k V (h.trans hj) (h.trans hk)).hom)
      (hc : ∀ j k l (U : X.Opens) (hj : U ≤ (i j).opensRange)
        (hk : U ≤ (i k).opensRange) (hl : U ≤ (i l).opensRange),
        (e j k U hj hk).hom ≫ (e k l U hk hl).hom = (e j l U hj hl).hom) :
      GeometricTransitionWitness (geometricTransition Y i M e)

variable (t : ∀ j k,
  ((pushforward (i j)).obj (M j)).over ((i j).opensRange ⊓ (i k).opensRange) ≅
    ((pushforward (i k)).obj (M k)).over ((i j).opensRange ⊓ (i k).opensRange))

/-- Eliminating the geometric witness proves the original section cocycle. -/
theorem GeometricTransitionWitness.cocycle (w : GeometricTransitionWitness Y i M t)
    (j k l : ι) (V : X.Opens) (hj : V ≤ (i j).opensRange)
    (hk : V ≤ (i k).opensRange) (hl : V ≤ (i l).opensRange)
    (s : Γ((pushforward (i j)).obj (M j), V)) :
    localEval (t k l).hom (le_inf hk hl) (localEval (t j k).hom (le_inf hj hk) s) =
      localEval (t j l).hom (le_inf hj hl) s := by
  cases w with
  | ofGeometric e hr hc =>
    exact geometricTransition_cocycle_eval Y i M e hr hc j k l V hj hk hl s

/-- Indexed geometric witnesses descend the original chart objects. -/
@[irreducible] def imageChartDataOfWitness (w : GeometricTransitionWitness Y i M t) :
    Data (fun j ↦ (i j).opensRange) :=
  imageChartData Y i M t (w.cocycle Y i M t)

/-- Witness-based descent recovers the module on every original chart. -/
@[irreducible] def imageChartPullbackIsoOfWitness
    (w : GeometricTransitionWitness Y i M t) (j : ι) :
    (pullback (i j)).obj (imageChartDataOfWitness Y i M t w).glued ≅ M j := by
  delta imageChartDataOfWitness
  exact imageChartPullbackIso Y i M t (w.cocycle Y i M t) j

end FLT.Mazur.ModuleSheafGluing

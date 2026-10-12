/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGeometricTransitionWitness

/-!
# Gluing module sheaves from geometric open transitions

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
/-- Geometric comparisons on all common subopens, with their pullback coherence. -/
structure GeometricOpenSystem where
  /-- The original chart comparison on each common subopen. -/
  iso : ∀ j k (U : X.Opens) (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange),
    (pullback (coordinate (i j) U hj)).obj (M j) ≅
      (pullback (coordinate (i k) U hk)).obj (M k)
  /-- Each comparison restricts to the comparison on every smaller open. -/
  refines : ∀ j k (U V : X.Opens) (h : V ≤ U)
    (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange),
    (pullback (X.homOfLE h)).map (iso j k U hj hk).hom ≫
        (comparison (X.homOfLE h) (coordinate (i k) U hk)
          (coordinate (i k) V (h.trans hk)) (coordinate_refine (i k) h hk)).hom.app (M k) =
      (comparison (X.homOfLE h) (coordinate (i j) U hj)
          (coordinate (i j) V (h.trans hj)) (coordinate_refine (i j) h hj)).hom.app (M j) ≫
        (iso j k V (h.trans hj) (h.trans hk)).hom
  /-- The original chart comparisons compose on every triple common subopen. -/
  cocycle : ∀ j k l (U : X.Opens) (hj : U ≤ (i j).opensRange)
    (hk : U ≤ (i k).opensRange) (hl : U ≤ (i l).opensRange),
    (iso j k U hj hk).hom ≫ (iso k l U hk hl).hom = (iso j l U hj hl).hom

variable (D : GeometricOpenSystem Y i M)

/-- The original geometric laws certify their actual ambient transition family. -/
theorem GeometricOpenSystem.witness :
    GeometricTransitionWitness Y i M (geometricTransition Y i M D.iso) :=
  .ofGeometric D.iso D.refines D.cocycle

/-- Geometric comparisons with their proved laws descend the original chart objects. -/
@[irreducible] def ofGeometricOpenSystem : Data (fun j ↦ (i j).opensRange) :=
  imageChartDataOfWitness Y i M (geometricTransition Y i M D.iso) (D.witness Y i M)

/-- The global sheaf recovers the original module on each original chart. -/
@[irreducible] def geometricOpenSystemPullbackIso (j : ι) :
    (pullback (i j)).obj (ofGeometricOpenSystem Y i M D).glued ≅ M j := by
  delta ofGeometricOpenSystem
  exact imageChartPullbackIsoOfWitness Y i M (geometricTransition Y i M D.iso)
    (D.witness Y i M) j

end FLT.Mazur.ModuleSheafGluing

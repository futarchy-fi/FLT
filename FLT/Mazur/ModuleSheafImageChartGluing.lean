/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluingTransport
public import FLT.Mazur.ModuleSheafOpenImageRecovery

/-!
# Gluing original open-immersion charts

Ambient transition isomorphisms with their proved section cocycle descend the
original chart modules. Pullback to each original chart recovers its module.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafGluing
open ModuleSheafOpenImageChart ModuleSheafMorphismGluing
universe u
variable {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u})
  (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)] (M : ∀ j, (Y j).Modules)
variable (t : ∀ j k,
  ((pushforward (i j)).obj (M j)).over ((i j).opensRange ⊓ (i k).opensRange) ≅
    ((pushforward (i k)).obj (M k)).over ((i j).opensRange ⊓ (i k).opensRange))
variable (hc : ∀ j k l (V : X.Opens) (hj : V ≤ (i j).opensRange)
  (hk : V ≤ (i k).opensRange) (hl : V ≤ (i l).opensRange)
  (s : Γ((pushforward (i j)).obj (M j), V)),
  localEval (t k l).hom (le_inf hk hl) (localEval (t j k).hom (le_inf hj hk) s) =
    localEval (t j l).hom (le_inf hj hl) s)
attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.pushforward
attribute [local irreducible] imageModule imagePushforwardIso

/-- Original open-immersion charts descend using their actual ambient transitions. -/
@[irreducible] def imageChartData : Data (fun j ↦ (i j).opensRange) :=
  ofPushforwardIsoEval (fun j ↦ (i j).opensRange)
    (fun j ↦ imageModule (i j) (M j)) (fun j ↦ (pushforward (i j)).obj (M j))
    (fun j ↦ imagePushforwardIso (i j) (M j)) t hc

/-- The descended sheaf recovers the original module on each original chart. -/
def imageChartPullbackIso (j : ι) :
    (pullback (i j)).obj (imageChartData Y i M t hc).glued ≅ M j := by
  unfold imageChartData
  exact pullbackRecovery (i j) (M j) _
    ((ofPushforwardIsoEval (fun j ↦ (i j).opensRange)
      (fun j ↦ imageModule (i j) (M j)) (fun j ↦ (pushforward (i j)).obj (M j))
      (fun j ↦ imagePushforwardIso (i j) (M j)) t hc).restrictionIso j)

end FLT.Mazur.ModuleSheafGluing

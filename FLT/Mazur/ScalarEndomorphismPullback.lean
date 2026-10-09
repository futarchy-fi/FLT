/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerScalarLift

/-!
# Pullback of scalar endomorphisms

The actual module pullback takes multiplication by a global function to
multiplication by its structural pullback. The adjunction checks this on units.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IdealPowerScalarLift
variable {X Y : Scheme.{u}}

/-- Pullback preserves scalar endomorphisms with the actual structural coefficient map. -/
lemma scalarEnd_pullback (f : X ⟶ Y) (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (pullback f).map (scalarEnd M r) = scalarEnd ((pullback f).obj M) (f.appTop r) := by
  apply ((pullbackPushforwardAdjunction f).homEquiv M _).injective
  change (pullbackPushforwardAdjunction f).unit.app M ≫
      (pushforward f).map ((pullback f).map (scalarEnd M r)) =
    (pullbackPushforwardAdjunction f).unit.app M ≫
      (pushforward f).map (scalarEnd ((pullback f).obj M) (f.appTop r))
  have hn := (pullbackPushforwardAdjunction f).unit.naturality (scalarEnd M r)
  change scalarEnd M r ≫ (pullbackPushforwardAdjunction f).unit.app M =
    (pullbackPushforwardAdjunction f).unit.app M ≫
      (pushforward f).map ((pullback f).map (scalarEnd M r)) at hn
  rw [← hn]
  apply Scheme.Modules.hom_ext
  intro U
  ext s : 2
  change ((pullbackPushforwardAdjunction f).unit.app M).app U
    (Y.presheaf.map U.leTop.op r • s) =
      X.presheaf.map (f ⁻¹ᵁ U).leTop.op (f.appTop r) •
        (show Γ((pullback f).obj M, f ⁻¹ᵁ U) from
          ((pullbackPushforwardAdjunction f).unit.app M).app U s)
  rw [Hom.app_smul]
  change f.app U (Y.presheaf.map U.leTop.op r) •
    (show Γ((pullback f).obj M, f ⁻¹ᵁ U) from
      ((pullbackPushforwardAdjunction f).unit.app M).app U s) = _
  congr 1
  exact congrArg (fun a ↦ a r) (f.naturality U.leTop.op)

end FLT.Mazur.IdealPowerScalarLift

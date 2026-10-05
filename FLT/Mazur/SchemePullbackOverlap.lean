/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIteratedPullbackSections

/-!
# Canonical geometric overlaps of pullback sheaves

Two projection paths with the same composite identify the corresponding
pullback sheaves. Their overlap preserves the iterated adjunction units.
Conjugating by a reconstruction chart preserves the same unit equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (l r : Z ⟶ Y) (k : Z ⟶ X)
variable (hl : l ≫ p = k) (hr : r ≫ p = k) (A : X.Modules)

/-- The canonical overlap between two pullback paths with the same composite. -/
def overlap : (pullback l).obj ((pullback p).obj A) ≅
    (pullback r).obj ((pullback p).obj A) :=
  compositeIso l p k hl A ≪≫ (compositeIso r p k hr A).symm

/-- The canonical overlap identifies the two iterated pullback unit sections. -/
theorem overlap_unit (m : Γ(A, ⊤)) :
    (overlap p l r k hl hr A).hom.app ⊤
      (((pullbackPushforwardAdjunction l).unit.app ((pullback p).obj A)).app ⊤
        (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m)) =
      ((pullbackPushforwardAdjunction r).unit.app ((pullback p).obj A)).app ⊤
        (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m) := by
  change (compositeIso r p k hr A).inv.app ⊤
    ((compositeIso l p k hl A).hom.app ⊤ _) = _
  rw [compositeIso_unit, ← compositeIso_unit r p k hr A m]
  exact congrArg (fun f ↦ f.app ⊤
    (((pullbackPushforwardAdjunction r).unit.app ((pullback p).obj A)).app ⊤
      (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m)))
    (compositeIso r p k hr A).hom_inv_id

variable {M : Y.Modules} (e : (pullback p).obj A ≅ M)

/-- Transport the canonical geometric overlap through a reconstruction chart. -/
def chartOverlap : (pullback l).obj M ≅ (pullback r).obj M :=
  ((pullback l).mapIso e).symm ≪≫ overlap p l r k hl hr A ≪≫ (pullback r).mapIso e

/-- The reconstructed overlap identifies the two lifts of each base section. -/
theorem chartOverlap_unit (m : Γ(A, ⊤)) :
    (chartOverlap p l r k hl hr A e).hom.app ⊤
      (((pullbackPushforwardAdjunction l).unit.app M).app ⊤
        (e.hom.app ⊤ (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m))) =
      ((pullbackPushforwardAdjunction r).unit.app M).app ⊤
        (e.hom.app ⊤ (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m)) := by
  have hl' := congrArg (fun f ↦ f.app ⊤
    (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m))
    ((pullbackPushforwardAdjunction l).unit.naturality e.hom)
  have hr' := congrArg (fun f ↦ f.app ⊤
    (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m))
    ((pullbackPushforwardAdjunction r).unit.naturality e.hom)
  change ((pullbackPushforwardAdjunction l).unit.app M).app ⊤
    (e.hom.app ⊤ (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m)) =
      ((pullback l).map e.hom).app ⊤
        (((pullbackPushforwardAdjunction l).unit.app ((pullback p).obj A)).app ⊤
          (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m)) at hl'
  change ((pullbackPushforwardAdjunction r).unit.app M).app ⊤
    (e.hom.app ⊤ (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m)) =
      ((pullback r).map e.hom).app ⊤
        (((pullbackPushforwardAdjunction r).unit.app ((pullback p).obj A)).app ⊤
          (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m)) at hr'
  rw [hl', hr']
  change ((pullback r).map e.hom).app ⊤
    ((overlap p l r k hl hr A).hom.app ⊤
      (((pullback l).map e.inv).app ⊤ (((pullback l).map e.hom).app ⊤ _))) = _
  have hi := congrArg (fun f ↦ f.app ⊤
    (((pullbackPushforwardAdjunction l).unit.app ((pullback p).obj A)).app ⊤
      (((pullbackPushforwardAdjunction p).unit.app A).app ⊤ m)))
    ((pullback l).mapIso e).hom_inv_id
  change ((pullback l).map e.inv).app ⊤ (((pullback l).map e.hom).app ⊤ _) = _ at hi
  simp only [Hom.id_app, ConcreteCategory.id_apply] at hi
  rw [hi, overlap_unit]
end FLT.Mazur.SchemePullbackOverlap

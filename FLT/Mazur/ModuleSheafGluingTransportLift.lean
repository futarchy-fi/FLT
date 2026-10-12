/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluingTransportProjection
public import FLT.Mazur.ModuleSheafGluingLift

/-!
# Lifting compatible maps to the original chart modules

The projections of transported gluing data obey the original transition
equation after the pushforward identifications are applied.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable (M : ∀ i, (U i).toScheme.Modules) (N : ι → X.Modules)
variable (e : ∀ i, (pushforward (U i).ι).obj (M i) ≅ N i)
variable (t : ∀ i j, (N i).over (U i ⊓ U j) ≅ (N j).over (U i ⊓ U j))
variable (hc : ∀ i j k V (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
  (s : Γ(N i, V)),
  ModuleSheafMorphismGluing.localEval (t j k).hom (le_inf hj hk)
      (ModuleSheafMorphismGluing.localEval (t i j).hom (le_inf hi hj) s) =
    ModuleSheafMorphismGluing.localEval (t i k).hom (le_inf hi hk) s)

variable {S : X.Modules}

/-- Maps from one ambient module compatible with the original chart transitions. -/
structure AmbientCone where
  /-- The complete original map to every chart pushforward. -/
  app : ∀ i, S ⟶ N i
  /-- The maps agree on the actual pair intersections. -/
  compatible : ∀ i j, (app i).over (U i ⊓ U j) ≫ (t i j).hom =
    (app j).over (U i ⊓ U j)

variable (a : AmbientCone U N t (S := S))

/-- Transporting a compatible cone retains its compatibility on all intersections. -/
theorem ambientCone_compatible (i j : ι) :
    (a.app i ≫ (e i).inv).over (U i ⊓ U j) ≫
        ((ofPushforwardIsoEval U M N e t hc).transition i j).hom =
      (a.app j ≫ (e j).inv).over (U i ⊓ U j) := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf (U i ⊓ U j)
  change F.map (a.app i ≫ (e i).inv) ≫
    (F.map (e i).hom ≫ (t i j).hom ≫ F.map (e j).inv) =
      F.map (a.app j ≫ (e j).inv)
  simp only [F.map_comp, Category.assoc]
  have he : F.map (e i).inv ≫ F.map (e i).hom = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
  rw [← Category.assoc (F.map (e i).inv) (F.map (e i).hom), he, Category.id_comp,
    ← Category.assoc (F.map (a.app i)) (t i j).hom, a.compatible i j]

/-- Compatible full original chart maps lift to the descended module sheaf. -/
@[irreducible] def ambientLift : S ⟶ (ofPushforwardIsoEval U M N e t hc).glued :=
  (ofPushforwardIsoEval U M N e t hc).lift (fun i ↦ a.app i ≫ (e i).inv)
    (ambientCone_compatible U M N e t hc a)

/-- Projection of the lift recovers every full original chart map. -/
@[reassoc] theorem ambientLift_projection (i : ι) :
    ambientLift U M N e t hc a ≫ ambientProjection U M N e t hc i = a.app i := by
  delta ambientLift ambientProjection
  rw [← Category.assoc, Data.lift_projection, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The full original chart maps determine the lift uniquely. -/
theorem ambientLift_unique (q : S ⟶ (ofPushforwardIsoEval U M N e t hc).glued)
    (hq : ∀ i, q ≫ ambientProjection U M N e t hc i = a.app i) :
    q = ambientLift U M N e t hc a := by
  apply Data.hom_ext_into_glued
  intro i
  apply (cancel_mono (e i).hom).mp
  simpa only [ambientProjection, Category.assoc] using
    (hq i).trans (ambientLift_projection U M N e t hc a i).symm

end FLT.Mazur.ModuleSheafGluing

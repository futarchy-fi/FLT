/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluingTransport

/-!
# Projections to the original ambient chart modules

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

/-- Projection from transported gluing into an original ambient chart module. -/
def ambientProjection (i : ι) : (ofPushforwardIsoEval U M N e t hc).glued ⟶ N i :=
  (ofPushforwardIsoEval U M N e t hc).projection i ≫ (e i).hom

/-- Original ambient transitions are recovered by the actual glued projections. -/
@[reassoc]
lemma ambientProjection_transition (i j : ι) :
    (ambientProjection U M N e t hc i).over (U i ⊓ U j) ≫ (t i j).hom =
      (ambientProjection U M N e t hc j).over (U i ⊓ U j) := by
  let A := ofPushforwardIsoEval U M N e t hc
  let F := SheafOfModules.overFunctor X.ringCatSheaf (U i ⊓ U j)
  have h := A.projection_transition i j
  change F.map (A.projection i) ≫
    (F.map (e i).hom ≫ (t i j).hom ≫ F.map (e j).inv) = F.map (A.projection j) at h
  have h' := congrArg (fun f ↦ f ≫ F.map (e j).hom) h
  simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id,
    F.map_id] at h'
  rw [Category.comp_id (t i j).hom] at h'
  change F.map (A.projection i ≫ (e i).hom) ≫ _ =
    F.map (A.projection j ≫ (e j).hom)
  simpa only [F.map_comp, Category.assoc] using h'

end FLT.Mazur.ModuleSheafGluing

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafEvaluatedGluing
public import FLT.Mazur.ModuleSheafLocalIsoTransport

/-!
# Transporting gluing comparisons to actual chart objects

Conjugating ambient transitions by pushforward identifications preserves
their sectionwise cocycle and supplies module-sheaf gluing data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafGluing
open ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable (M : ∀ i, (U i).toScheme.Modules) (N : ι → X.Modules)
variable (e : ∀ i, (pushforward (U i).ι).obj (M i) ≅ N i)
variable (t : ∀ i j, (N i).over (U i ⊓ U j) ≅ (N j).over (U i ⊓ U j))

/-- Ambient transition isomorphisms transferred to the chart pushforwards. -/
def transportedTransition (i j : ι) :
    ((pushforward (U i).ι).obj (M i)).over (U i ⊓ U j) ≅
      ((pushforward (U j).ι).obj (M j)).over (U i ⊓ U j) :=
  (SheafOfModules.overFunctor X.ringCatSheaf (U i ⊓ U j)).mapIso (e i) ≪≫
    t i j ≪≫ ((SheafOfModules.overFunctor X.ringCatSheaf (U i ⊓ U j)).mapIso (e j)).symm

/-- A proved ambient cocycle gives gluing data for the original chart objects. -/
def ofPushforwardIso
    (hc : ∀ i j k V (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) (s : Γ(N i, V)),
      localApp (t j k).hom (le_inf hj hk) (localApp (t i j).hom (le_inf hi hj) s) =
        localApp (t i k).hom (le_inf hi hk) s) : Data U where
  obj := M
  transition := transportedTransition U M N e t
  cocycle i j k V hi hj hk s := by
    simp only [transportedTransition, localApp_iso_conjugate]
    have he (z : Γ(N j, V)) : (e j).hom.app V ((e j).inv.app V z) = z :=
      congrArg (fun f ↦ f.app V z) (e j).inv_hom_id
    rw [he, hc i j k V hi hj hk]

/-- Sealed ambient section cocycles also transfer to the original chart objects. -/
def ofPushforwardIsoEval
    (hc : ∀ i j k V (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) (s : Γ(N i, V)),
      localEval (t j k).hom (le_inf hj hk) (localEval (t i j).hom (le_inf hi hj) s) =
        localEval (t i k).hom (le_inf hi hk) s) : Data U :=
  ofPushforwardIso U M N e t (fun i j k V hi hj hk s ↦ by
    simpa only [localEval] using hc i j k V hi hj hk s)

end FLT.Mazur.ModuleSheafGluing

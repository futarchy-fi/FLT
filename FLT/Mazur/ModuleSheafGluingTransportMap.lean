/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluingTransport
public import FLT.Mazur.ModuleSheafLocalNaturality

/-!
# Transporting compatible morphisms of gluing data

Ambient maps commuting with comparison isomorphisms induce compatible maps
of the original chart objects through their pushforward identifications.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafGluing
open ModuleSheafMorphismGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
variable (M M' : ∀ i, (U i).toScheme.Modules) (N N' : ι → X.Modules)
variable (e : ∀ i, (pushforward (U i).ι).obj (M i) ≅ N i)
variable (e' : ∀ i, (pushforward (U i).ι).obj (M' i) ≅ N' i)
variable (t : ∀ i j, (N i).over (U i ⊓ U j) ≅ (N j).over (U i ⊓ U j))
variable (t' : ∀ i j, (N' i).over (U i ⊓ U j) ≅ (N' j).over (U i ⊓ U j))
variable (hc : ∀ i j k V (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k) (s : Γ(N i, V)),
  localEval (t j k).hom (le_inf hj hk) (localEval (t i j).hom (le_inf hi hj) s) =
    localEval (t i k).hom (le_inf hi hk) s)
variable (hc' : ∀ i j k V (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
  (s : Γ(N' i, V)),
  localEval (t' j k).hom (le_inf hj hk) (localEval (t' i j).hom (le_inf hi hj) s) =
    localEval (t' i k).hom (le_inf hi hk) s)

/-- Compatible ambient maps transport to a morphism of actual chart gluing data. -/
def ofPushforwardIsoEvalMap (a : ∀ i, M i ⟶ M' i) (b : ∀ i, N i ⟶ N' i)
    (he : ∀ i, (pushforward (U i).ι).map (a i) ≫ (e' i).hom = (e i).hom ≫ b i)
    (ht : ∀ i j V (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(N i, V)),
      localEval (t' i j).hom (le_inf hi hj) ((b i).app V s) =
        (b j).app V (localEval (t i j).hom (le_inf hi hj) s)) :
    (ofPushforwardIsoEval U M N e t hc).Map
      (ofPushforwardIsoEval U M' N' e' t' hc') where
  app := a
  compatible i j V hi hj s := by
    change localApp (transportedTransition U M' N' e' t' i j).hom (le_inf hi hj)
        (((pushforward (U i).ι).map (a i)).app V s) =
      ((pushforward (U j).ι).map (a j)).app V
        (localApp (transportedTransition U M N e t i j).hom (le_inf hi hj) s)
    rw [← localEval, ← localEval]
    simp only [transportedTransition, localEval_conjugate]
    have hi' := congrArg (fun f ↦ f.app V s) (he i)
    change (e' i).hom.app V (((pushforward (U i).ι).map (a i)).app V s) =
      (b i).app V ((e i).hom.app V s) at hi'
    rw [hi', ht i j V hi hj]
    have hj' : b j ≫ (e' j).inv =
        (e j).inv ≫ (pushforward (U j).ι).map (a j) := by
      apply (cancel_epi (e j).hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← he j, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact congrArg (fun f ↦ f.app V
      (localEval (t i j).hom (le_inf hi hj) ((e i).hom.app V s))) hj'

end FLT.Mazur.ModuleSheafGluing

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapNormalizationNaturality
public import FLT.Mazur.ModuleSheafOpenImmersionGluing

/-!
# Detecting compatible maps on normalized overlap charts

The normalization comparisons are invertible, so a normalized square
detects the original pulled-back square. An open cover then detects it globally.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SchemeOverlapDiagonalChart
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y Z T : Scheme.{u}}

/-- A compatible normalized square detects the unnormalized pullback square. -/
lemma pullback_compatible_of_normalize (l r : Z ⟶ Y) (k : T ⟶ Z)
    (l' r' : T ⟶ Y) (wl : k ≫ l = l') (wr : k ≫ r = r')
    {M N : Y.Modules} (e : (pullback l).obj M ≅ (pullback r).obj M)
    (e' : (pullback l).obj N ≅ (pullback r).obj N) (f : M ⟶ N)
    (h : (normalize l r k l' r' wl wr M e).hom ≫ (pullback r').map f =
      (pullback l').map f ≫ (normalize l r k l' r' wl wr N e').hom) :
    (pullback k).map (e.hom ≫ (pullback r).map f) =
      (pullback k).map ((pullback l).map f ≫ e'.hom) := by
  have hl := (comparison k l l' wl).inv.naturality f
  have hr := (comparison k r r' wr).hom.naturality f
  dsimp only [Functor.comp_map] at hl hr
  apply (cancel_epi ((comparison k l l' wl).inv.app M)).mp
  apply (cancel_mono ((comparison k r r' wr).hom.app N)).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [hr, ← Category.assoc ((comparison k l l' wl).inv.app M)
    ((pullback k).map ((pullback l).map f)), ← hl]
  simpa only [SchemeOverlapDiagonalChart.normalize, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h

/-- Compatibility of normalized squares on an open cover detects the global square. -/
lemma compatible_of_normalized_cover (l r : Z ⟶ Y) {ι : Type v}
    (T : ι → Scheme.{u}) (k : ∀ i, T i ⟶ Z) [∀ i, IsOpenImmersion (k i)]
    (hk : ∀ x : Z, ∃ i, x ∈ Set.range (k i))
    (l' r' : ∀ i, T i ⟶ Y) (wl : ∀ i, k i ≫ l = l' i) (wr : ∀ i, k i ≫ r = r' i)
    {M N : Y.Modules} (e : (pullback l).obj M ≅ (pullback r).obj M)
    (e' : (pullback l).obj N ≅ (pullback r).obj N) (f : M ⟶ N)
    (h : ∀ i, (normalize l r (k i) (l' i) (r' i) (wl i) (wr i) M e).hom ≫
      (pullback (r' i)).map f = (pullback (l' i)).map f ≫
        (normalize l r (k i) (l' i) (r' i) (wl i) (wr i) N e').hom) :
    e.hom ≫ (pullback r).map f = (pullback l).map f ≫ e'.hom :=
  ModuleSheafOpenImmersionGluing.hom_ext T k hk _ _ (fun i ↦
    pullback_compatible_of_normalize l r (k i) (l' i) (r' i) (wl i) (wr i) e e' f (h i))

end FLT.Mazur.SchemeOverlapDiagonalChart

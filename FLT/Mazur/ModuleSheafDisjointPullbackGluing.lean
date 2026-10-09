/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDisjointGluing
public import FLT.Mazur.ModuleSheafOpenImmersionGluing

/-!
# Independent pullback maps on disjoint open-immersion covers

Disjointness supplies compatibility for every family of pullback maps.
Independent isomorphisms glue and retain their prescribed restrictions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.ModuleSheafDisjointPullbackGluing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v}
variable (Y : ι → Scheme.{u}) (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (hd : Pairwise (fun j k ↦ Disjoint (i j).opensRange (i k).opensRange))
variable (hc : ∀ x : X, ∃ j, x ∈ Set.range (i j))

include hd in
/-- Independent pullback maps on distinct components have empty compatibility conditions. -/
lemma compatible (f : ∀ j, (pullback (i j)).obj M ⟶ (pullback (i j)).obj N) :
    ModuleSheafOpenImmersionGluing.Compatible Y i f := by
  intro j k V hj hk
  by_cases h : j = k
  · subst k; rfl
  · ext s
    have hV : V = ⊥ := le_bot_iff.mp ((le_inf hj hk).trans_eq (hd h).eq_bot)
    exact @Subsingleton.elim Γ(N, V)
      (ModuleSheafEmptySlice.sections_subsingleton N V hV) _ _

/-- Glue arbitrary component isomorphisms on a disjoint open-immersion cover. -/
def glueIso (e : ∀ j, (pullback (i j)).obj M ≅ (pullback (i j)).obj N) : M ≅ N :=
  ModuleSheafOpenImmersionGluing.glueIso Y i hc (fun j ↦ (e j).hom)
    (compatible Y i hd _) (fun _ ↦ inferInstance)

/-- The constructed isomorphism restricts to each prescribed component isomorphism. -/
lemma pullback_glueIso (e : ∀ j, (pullback (i j)).obj M ≅ (pullback (i j)).obj N)
    (j : ι) : (pullback (i j)).map (glueIso Y i hd hc e).hom = (e j).hom :=
  ModuleSheafOpenImmersionGluing.pullback_glue Y i hc _ (compatible Y i hd _) j

end FLT.Mazur.ModuleSheafDisjointPullbackGluing

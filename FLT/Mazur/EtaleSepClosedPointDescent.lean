/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnramifiedSectionImmersion
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Exact descent of étale points to a separably closed field

Every point over a larger field on an étale scheme over a separably closed
field is the base extension of an actual rational section. The section is
open, and the factorization recovers the whole morphism, not just its image.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtaleSepClosedPointDescent
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [IsSepClosed k] {X : Scheme}

/-- An étale geometric point descends exactly to an open rational section over the base field. -/
theorem exists_section (f : X ⟶ Spec (.of k)) [Etale f] (φ : k →+* K)
    (x : Spec (.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom φ)) :
    ∃ y : Spec (.of k) ⟶ X,
      y ≫ f = 𝟙 _ ∧ IsOpenImmersion y ∧ Spec.map (CommRingCat.ofHom φ) ≫ y = x := by
  obtain ⟨y, hy, hyp⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f (𝟙 (Spec (.of k)))
    (x default) (Subsingleton.elim _ _)
  let _ := UnramifiedSectionImmersion.isOpenImmersion f y hy
  have hr : Set.range x ⊆ Set.range y := by
    rintro _ ⟨w, rfl⟩
    exact ⟨default, hyp.trans (congrArg x (Subsingleton.elim _ _))⟩
  let a := IsOpenImmersion.lift y x hr
  have ha : a ≫ y = x := IsOpenImmersion.lift_fac y x hr
  have hb : a = Spec.map (CommRingCat.ofHom φ) := by
    calc
      a = a ≫ (y ≫ f) := by rw [hy, Category.comp_id]
      _ = _ := by rw [← Category.assoc, ha, hx]
  exact ⟨y, hy, inferInstance, hb ▸ ha⟩

/-- Matching étale coordinates descend the entire point to a separably closed coefficient field. -/
theorem exists_factor {A : Scheme} (g : X ⟶ A) [Etale g]
    (t : Spec (.of k) ⟶ A) (φ : k →+* K) (x : Spec (.of K) ⟶ X)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ t) :
    ∃ y : Spec (.of k) ⟶ X,
      y ≫ g = t ∧ Spec.map (CommRingCat.ofHom φ) ≫ y = x := by
  let z := pullback.lift x (Spec.map (CommRingCat.ofHom φ)) hx
  obtain ⟨s, hs, _, hz⟩ := exists_section (pullback.snd g t) φ z
    (pullback.lift_snd _ _ _)
  refine ⟨s ≫ pullback.fst g t, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · rw [← Category.assoc, hz]
    exact pullback.lift_fst _ _ _

end FLT.Mazur.EtaleSepClosedPointDescent

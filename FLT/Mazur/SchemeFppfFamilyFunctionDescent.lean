/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfCoverInvariantFunctions

/-!
# Effective descent of functions from an arbitrary fppf covering family

Pairwise coefficient equations on actual fiber products produce a unique
function on the original target, with no finiteness assumption on the family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SchemeEffectiveEpiSections
variable {X : Scheme.{u}} (C : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- The actual fppf family is effective epimorphic, not only jointly surjective. -/
theorem effectiveEpiFamily : EffectiveEpiFamily C.X C.f := by
  rw [← Sieve.effectiveEpimorphic_family,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Y
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
    (Precoverage.generate_mem_toGrothendieck C.mem₀)

/-- Functions compatible after every scheme test descend uniquely along the whole family. -/
theorem family_sections_existsUnique (s : ∀ a, Γ(C.X a, ⊤))
    (hs : ∀ (T : Scheme.{u}) (a b : C.I₀) (g : T ⟶ C.X a) (h : T ⟶ C.X b),
      g ≫ C.f a = h ≫ C.f b → g.appTop (s a) = h.appTop (s b)) :
    ∃! t : Γ(X, ⊤), ∀ a, (C.f a).appTop t = s a := by
  let _ := effectiveEpiFamily C
  let k := fun a ↦ (functionEquiv (C.X a)).symm (s a)
  have hk : ∀ (T : Scheme.{u}) (a b : C.I₀) (g : T ⟶ C.X a) (h : T ⟶ C.X b),
      g ≫ C.f a = h ≫ C.f b → g ≫ k a = h ≫ k b := by
    intro T a b g h hh
    apply (functionEquiv T).injective
    simpa only [functionEquiv_comp, k, Equiv.apply_symm_apply] using hs T a b g h hh
  let t := functionEquiv X (EffectiveEpiFamily.desc C.X C.f k (fun {_} ↦ hk _))
  have ht (a : C.I₀) : (C.f a).appTop t = s a := by
    dsimp only [t]
    rw [← functionEquiv_comp, EffectiveEpiFamily.fac]
    exact (functionEquiv (C.X a)).apply_symm_apply (s a)
  refine ⟨t, ht, fun z hz ↦ ?_⟩
  exact cover_sections_ext C (fun a ↦ (hz a).trans (ht a).symm)

/-- It suffices to check compatibility on the actual pairwise fiber products. -/
theorem family_sections_existsUnique_of_pullback (s : ∀ a, Γ(C.X a, ⊤))
    (hs : ∀ a b, (pullback.fst (C.f a) (C.f b)).appTop (s a) =
      (pullback.snd (C.f a) (C.f b)).appTop (s b)) :
    ∃! t : Γ(X, ⊤), ∀ a, (C.f a).appTop t = s a := by
  apply family_sections_existsUnique C s
  intro T a b g h hh
  have he := congrArg (fun v ↦ (pullback.lift g h hh).appTop v) (hs a b)
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    pullback.lift_fst, pullback.lift_snd] using he

/-- Tests with both endpoints in covering charts detect the entire original relation equation. -/
theorem relation_eq_of_chart_tests {D : Scheme.{u}} (p q : D ⟶ X) (s : Γ(X, ⊤))
    (h : ∀ (T : Scheme.{u}) (a b : C.I₀) (g : T ⟶ C.X a) (k : T ⟶ C.X b)
      (w : T ⟶ D), w ≫ p = g ≫ C.f a → w ≫ q = k ≫ C.f b →
        g.appTop ((C.f a).appTop s) = k.appTop ((C.f b).appTop s)) :
    p.appTop s = q.appTop s := by
  apply cover_sections_ext (C.pullback₁ p)
  intro a
  apply cover_sections_ext (C.pullback₁ (pullback.fst p (C.f a) ≫ q))
  intro b
  let l := pullback.fst (pullback.fst p (C.f a) ≫ q) (C.f b)
  let r := pullback.snd (pullback.fst p (C.f a) ≫ q) (C.f b)
  have hp : (l ≫ pullback.fst p (C.f a)) ≫ p =
      (l ≫ pullback.snd p (C.f a)) ≫ C.f a := by
    simp only [Category.assoc, pullback.condition]
  have hq : (l ≫ pullback.fst p (C.f a)) ≫ q = r ≫ C.f b := by
    rw [Category.assoc]
    exact pullback.condition
  have he := h _ a b (l ≫ pullback.snd p (C.f a)) r
    (l ≫ pullback.fst p (C.f a)) hp hq
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop] at he ⊢
  change (l ≫ pullback.fst p (C.f a) ≫ p).appTop s =
    (l ≫ pullback.fst p (C.f a) ≫ q).appTop s
  simpa only [← Category.assoc, hp, hq] using he

end FLT.Mazur.SchemeFppfFamily

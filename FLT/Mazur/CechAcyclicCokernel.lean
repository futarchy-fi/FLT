/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeOpen
public import FLT.Mazur.CechSheafHZero
public import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Acyclic cokernels and exact Cech terms

The Ext long exact sequence preserves cover acyclicity under cokernels of
embeddings into injectives. Vanishing of first cohomology on cover intersections
makes sections surjective, and arbitrary products give short exact Cech terms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace FLT.Mazur.CechAcyclicCokernel

open CechFreeOpen CechSheafHZero

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

local instance cechAcyclicCokernelInst1 : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- All positive Ext cohomology vanishes on each finite cover intersection. -/
def CoverAcyclic (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ (n q : ℕ) (a : Fin (n + 1) → ι), Subsingleton (F.H' (q + 1) (V U n a))

/-- An injective coefficient sheaf is acyclic on every cover intersection. -/
lemma coverAcyclic_of_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective F] :
    CoverAcyclic U F := by
  intro n q a
  exact subsingleton_of_forall_eq 0 fun x ↦ Abelian.Ext.eq_zero_of_injective x

/-- The cokernel of an acyclic sheaf in an injective sheaf is acyclic. -/
lemma coverAcyclic_cokernel {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [Injective S.X₂] (hF : CoverAcyclic U S.X₁) :
    CoverAcyclic U S.X₃ := by
  intro n q a
  have : Subsingleton (Abelian.Ext.{u + 1} (freeOpen (V U n a)) S.X₁
      (q + 1 + 1)) := hF n (q + 1) a
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₃ (freeOpen (V U n a)) hS x
    rfl (Subsingleton.elim _ 0)
  rw [Abelian.Ext.eq_zero_of_injective y, Abelian.Ext.zero_comp] at hy
  exact hy.symm

/-- Vanishing of first cohomology removes the obstruction to lifting a section. -/
lemma sections_surjective_of_hPrime_one
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (W : Opens X) [Subsingleton (S.X₁.H' 1 W)] :
    Function.Surjective (S.g.hom.app (op W)) := by
  have : Subsingleton (Abelian.Ext.{u + 1} (freeOpen W) S.X₁ 1) :=
    inferInstanceAs (Subsingleton (S.X₁.H' 1 W))
  intro s
  obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₃ (freeOpen W) hS
    ((hPrimeZeroEquiv W S.X₃).symm s) rfl (Subsingleton.elim _ 0)
  refine ⟨hPrimeZeroEquiv W S.X₂ x, ?_⟩
  rw [← hPrimeZeroEquiv_naturality]
  change hPrimeZeroEquiv W S.X₃ (x.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)) = s
  rw [hx, AddEquiv.apply_symm_apply]

omit [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Cech term coordinates commute with every coefficient morphism. -/
lemma termEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (x : (C U F).X n) (a : Fin (n + 1) → ι) :
    termEquiv U G n (((cechComplexFunctor U).map f.hom).f n x) a =
      f.hom.app (op (V U n a)) (termEquiv U F n x a) := by
  rw [termEquiv_apply, termEquiv_apply]
  change G.obj.map _ (Pi.π (fun b : Fin (n + 1) → ι ↦
    G.obj.obj (op (∏ᶜ (U ∘ b)))) a
    ((Limits.Pi.map (fun b : Fin (n + 1) → ι ↦ f.hom.app (op (∏ᶜ (U ∘ b))))) x)) = _
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  apply ConcreteCategory.congr_hom
  rw [← Category.assoc, Pi.map_π, Category.assoc, f.hom.naturality]

/-- Acyclicity of the first coefficient makes every Cech term short exact. -/
lemma cech_degree_shortExact {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hF : CoverAcyclic U S.X₁) (n : ℕ) :
    (ShortComplex.mk (((cechComplexFunctor U).map S.f.hom).f n)
      (((cechComplexFunctor U).map S.g.hom).f n) (by
        ext x
        apply (termEquiv U S.X₃ n).injective
        funext a
        change termEquiv U S.X₃ n
          (((cechComplexFunctor U).map S.g.hom).f n
            (((cechComplexFunctor U).map S.f.hom).f n x)) a = _
        rw [termEquiv_naturality, termEquiv_naturality]
        change _ = termEquiv U S.X₃ n 0 a
        rw [map_zero]
        have hz : S.f.hom ≫ S.g.hom = 0 :=
          congrArg (fun f : S.X₁ ⟶ S.X₃ ↦ f.hom) S.zero
        exact ConcreteCategory.congr_hom (NatTrans.congr_app hz (op (V U n a))) _)).ShortExact := by
  have := hS.mono_f
  have : Mono S.f.hom := Functor.map_mono (sheafToPresheaf _ _) S.f
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.ab_exact_iff]
    intro s hs
    have hlift (a : Fin (n + 1) → ι) :
        ∃ t, S.f.hom.app (op (V U n a)) t = termEquiv U S.X₂ n s a := by
      apply TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f
      rw [← termEquiv_naturality, hs, map_zero]
      rfl
    choose t ht using hlift
    refine ⟨(termEquiv U S.X₁ n).symm t, ?_⟩
    apply (termEquiv U S.X₂ n).injective
    funext a
    rw [termEquiv_naturality, AddEquiv.apply_symm_apply]
    exact ht a
  · apply (AddCommGrpCat.mono_iff_injective _).mpr
    intro s t h
    apply (termEquiv U S.X₁ n).injective
    funext a
    apply (AddCommGrpCat.mono_iff_injective (S.f.hom.app (op (V U n a)))).mp
      inferInstance
    rw [← termEquiv_naturality, ← termEquiv_naturality, h]
  · apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    have hlift (a : Fin (n + 1) → ι) :
        ∃ t, S.g.hom.app (op (V U n a)) t = termEquiv U S.X₃ n s a := by
      have := hF n 0 a
      exact sections_surjective_of_hPrime_one hS (V U n a) _
    choose t ht using hlift
    refine ⟨(termEquiv U S.X₂ n).symm t, ?_⟩
    apply (termEquiv U S.X₃ n).injective
    funext a
    rw [termEquiv_naturality, AddEquiv.apply_symm_apply]
    exact ht a

end FLT.Mazur.CechAcyclicCokernel

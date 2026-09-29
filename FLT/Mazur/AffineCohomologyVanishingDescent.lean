/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechAcyclicCokernel

/-!
# Descent of local lifts from first Cech exactness

In a short exact sequence of abelian sheaves, local lifts of a section differ
by a Cech cocycle in the kernel. Exactness in Cech degree one corrects the lifts
to a compatible family, which glues. No higher sheaf cohomology vanishing is
required for this argument.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace FLT.Mazur.AffineCohomologyVanishingDescent

open CechSheafHZero CechAcyclicCokernel

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- The coefficient map on a Cech term. -/
abbrev termMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :=
  ((cechComplexFunctor U).map f.hom).f n

/-- Coefficient maps commute with the Cech differential. -/
lemma termMap_d {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (p q : ℕ) (x : (C U F).X p) :
    termMap U f q ((C U F).d p q x) = (C U G).d p q (termMap U f p x) :=
  ConcreteCategory.congr_hom (((cechComplexFunctor U).map f.hom).comm p q).symm x

/-- A monomorphism of sheaves is injective on every Cech term. -/
lemma termMap_injective {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) [Mono f] (n : ℕ) : Function.Injective (termMap U f n) := by
  have : Mono f.hom := Functor.map_mono (sheafToPresheaf _ _) f
  intro x y h
  apply (termEquiv U F n).injective
  funext a
  apply (AddCommGrpCat.mono_iff_injective (f.hom.app (op (V U n a)))).mp inferInstance
  rw [← termEquiv_naturality, ← termEquiv_naturality, h]

/-- Taking Cech terms preserves exactness at the middle of a short exact sequence. -/
lemma termMap_exact {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (termMap U S.f n) (termMap U S.g n) := by
  intro x
  constructor
  · intro hx
    have hlift (a : Fin (n + 1) → ι) :
        ∃ y, S.f.hom.app (op (V U n a)) y = termEquiv U S.X₂ n x a := by
      apply TopCat.Sheaf.sections_exact_of_left_exact hS.exact hS.mono_f
      rw [← termEquiv_naturality, hx, map_zero]
      rfl
    choose y hy using hlift
    refine ⟨(termEquiv U S.X₁ n).symm y, ?_⟩
    apply (termEquiv U S.X₂ n).injective
    funext a
    rw [termEquiv_naturality, AddEquiv.apply_symm_apply]
    exact hy a
  · rintro ⟨y, rfl⟩
    apply (termEquiv U S.X₃ n).injective
    funext a
    rw [termEquiv_naturality, termEquiv_naturality, map_zero]
    have hz : S.f.hom ≫ S.g.hom = 0 :=
      congrArg (fun f : S.X₁ ⟶ S.X₃ ↦ f.hom) S.zero
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hz (op (V U n a))) _

/-- A lifted zero-cocycle can be corrected when first Cech cohomology vanishes. -/
lemma lift_zero_cocycle {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hF : (C U S.X₁).ExactAt 1)
    (z : (C U S.X₃).X 0) (hz : (C U S.X₃).d 0 1 z = 0)
    (y : (C U S.X₂).X 0) (hy : termMap U S.g 0 y = z) :
    ∃ t : (C U S.X₂).X 0, (C U S.X₂).d 0 1 t = 0 ∧ termMap U S.g 0 t = z := by
  have := hS.mono_f
  obtain ⟨b, hb⟩ := (termMap_exact U hS 1 ((C U S.X₂).d 0 1 y)).mp (by
    rw [termMap_d, hy, hz])
  have hbclosed : (C U S.X₁).d 1 2 b = 0 := by
    apply termMap_injective U S.f 2
    rw [termMap_d, hb, map_zero, ← ConcreteCategory.comp_apply,
      HomologicalComplex.d_comp_d]
    rfl
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hF
  obtain ⟨c, hc⟩ := hF b hbclosed
  change (C U S.X₁).d 0 1 c = b at hc
  refine ⟨y - termMap U S.f 0 c, ?_, ?_⟩
  · rw [map_sub, ← termMap_d, hc, hb, sub_self]
  · rw [map_sub, hy, (termMap_exact U hS 0 _).mpr ⟨c, rfl⟩, sub_zero]

/-- First Cech exactness glues local lifts to a global lift. -/
lemma exists_section_lift {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (hU : iSup U = ⊤) (hF : (C U S.X₁).ExactAt 1)
    (s : S.X₃.obj.obj (op ⊤)) (t : ∀ i, S.X₂.obj.obj (op (U i)))
    (ht : ∀ i, S.g.hom.app (op (U i)) (t i) =
      S.X₃.obj.map (homOfLE le_top).op s) :
    ∃ r : S.X₂.obj.obj (op ⊤), S.g.hom.app (op ⊤) r = s := by
  let z := (zeroTermEquiv U S.X₃).symm (CechSheafH.restrictZero S.X₃ U s).val
  have hz : (C U S.X₃).d 0 1 z = 0 := by
    apply (coordinates_mem_iff U S.X₃ z).mp
    simpa only [z, AddEquiv.apply_symm_apply] using
      (CechSheafH.restrictZero S.X₃ U s).property
  let y := (zeroTermEquiv U S.X₂).symm t
  have hy : termMap U S.g 0 y = z := by
    apply (zeroTermEquiv U S.X₃).injective
    funext i
    rw [zeroTermEquiv_naturality]
    change S.g.hom.app (op (U i)) ((zeroTermEquiv U S.X₂) ((zeroTermEquiv U S.X₂).symm t) i)
      = ((zeroTermEquiv U S.X₃) ((zeroTermEquiv U S.X₃).symm _) i)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact ht i
  obtain ⟨b, hb, hgb⟩ := lift_zero_cocycle U hS hF z hz y hy
  obtain ⟨r, hr, _⟩ := S.X₂.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (ge_of_eq hU) (zeroTermEquiv U S.X₂ b) ((d_zero_iff_compatible U S.X₂ b).mp hb)
  refine ⟨r, ?_⟩
  apply S.X₃.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) (ge_of_eq hU)
  intro i
  rw [← NatTrans.naturality_apply, hr i, ← zeroTermEquiv_naturality, hgb]
  exact congrFun ((zeroTermEquiv U S.X₃).apply_symm_apply _) i

end FLT.Mazur.AffineCohomologyVanishingDescent

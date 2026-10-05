/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Direct sums on sites with finite subcovers

A covering sieve with a finite covering subfamily bounds the support of a
degreewise gluing. Thus pointwise direct sums of abelian sheaves are sheaves
on such a site. No compactness assertion about arbitrary opens is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open scoped DirectSum

universe u

namespace FLT.Mazur.FiniteCoverDirectSum

variable {C : Type u} [SmallCategory C]

/-- Arrows belonging to a sieve, with their domains. -/
abbrev CoverArrow {U : C} (S : Sieve U) := Σ V, { f : V ⟶ U // S f }

/-- The presieve consisting of a selected finite subfamily. -/
def finitePresieve {U : C} {S : Sieve U} (s : Finset (CoverArrow S)) : Presieve U :=
  Presieve.ofArrows (fun i : s ↦ i.val.1) (fun i ↦ i.val.2.val)

/-- The pointwise direct sum, with the original degreewise restrictions. -/
abbrev presheaf (P : ℕ → Cᵒᵖ ⥤ AddCommGrpCat.{u}) : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (⨁ n, P n |>.obj U)
  map f := AddCommGrpCat.ofHom (DirectSum.map (fun n ↦ (P n |>.map f).hom))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro s
    ext n
    exact ConcreteCategory.congr_hom ((P n).map_id U) (s n)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    ext n
    exact ConcreteCategory.congr_hom ((P n).map_comp f g) (s n)

/-- Restriction is computed separately in every original degree. -/
lemma map_apply (P : ℕ → Cᵒᵖ ⥤ AddCommGrpCat.{u}) {U V : Cᵒᵖ}
    (f : U ⟶ V) (s : (presheaf P).obj U) (n : ℕ) :
    (presheaf P).map f s n = (P n).map f (s n) :=
  DirectSum.map_apply _ _ _

/-- Finite subcovers suffice to glue the actual pointwise direct sum. -/
theorem isSheaf (J : GrothendieckTopology C)
    (hfinite : ∀ (U : C) (S : Sieve U), S ∈ J U →
      ∃ s : Finset (CoverArrow S), Sieve.generate (finitePresieve s) ∈ J U)
    (P : ℕ → Cᵒᵖ ⥤ AddCommGrpCat.{u}) (hP : ∀ n, Presheaf.IsSheaf J (P n)) :
    Presheaf.IsSheaf J (presheaf P) := by
  classical
  rw [Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type]
  have hp (n : ℕ) : Presieve.IsSheaf J (P n ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type J _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat)).mp (hP n))
  intro U S hS x hx
  let xn (n : ℕ) : Presieve.FamilyOfElements (P n ⋙ forget AddCommGrpCat) S.arrows :=
    fun V f hf ↦ DFinsupp.toFun (x f hf) n
  have hxn (n : ℕ) : (xn n).Compatible := by
    intro V W T a b f g hf hg hab
    exact congrArg (fun s : ⨁ k, (P k).obj (.op T) ↦ s n) (hx a b hf hg hab)
  let g (n : ℕ) := (hp n S hS).amalgamate (xn n) (hxn n)
  have hg (n : ℕ) {V : C} (f : V ⟶ U) (hf : S f) :
      (P n).map f.op (g n) = DFinsupp.toFun (x f hf) n :=
    (hp n S hS).valid_glue (hxn n) f hf
  obtain ⟨s, hs⟩ := hfinite U S hS
  let support : Finset ℕ := s.biUnion (fun i ↦
    DFinsupp.support (x i.2.val i.2.property))
  have hgzero (n : ℕ) (hn : n ∉ support) : g n = 0 := by
    apply ((hp n).isSheafFor (finitePresieve s) hs).isSeparatedFor.ext
    intro V f hf
    cases hf with
    | mk i =>
      change (P n).map i.val.2.val.op (g n) = (P n).map i.val.2.val.op 0
      rw [hg n _ i.val.2.property, map_zero]
      apply DFinsupp.notMem_support_iff.mp
      intro hn'
      exact hn (Finset.mem_biUnion.mpr ⟨i.val, i.property, hn'⟩)
  let t : (presheaf P).obj (.op U) :=
    ⟨g, Trunc.mk ⟨support.val, fun n ↦ by
      by_cases hn : n ∈ support
      · exact Or.inl hn
      · exact Or.inr (hgzero n hn)⟩⟩
  refine ⟨t, ?_, ?_⟩
  · intro V f hf
    apply DFinsupp.ext
    intro n
    exact hg n f hf
  · intro y hy
    apply DFinsupp.ext
    intro n
    apply (hp n S hS).isSeparatedFor.ext
    intro V f hf
    exact (congrArg (fun z : ⨁ k, (P k).obj (.op V) ↦ z n) (hy f hf)).trans (hg n f hf).symm

end FLT.Mazur.FiniteCoverDirectSum

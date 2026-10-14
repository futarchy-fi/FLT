/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.KernelPairGenericBranchInverses
public import FLT.Mazur.KernelPairEffectiveUnramified
public import FLT.Mazur.MonomorphismFlatInverseImage

/-!
# An exact source-branch criterion for nonempty effective fppf regions

A represented point constructs an open original source branch etale over the
unrestricted target. Conversely, one such branch and point coverage of the
whole generic kernel construct a represented point. This identifies the exact
remaining seed geometry without assuming generic inverse morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.KernelPairEffectiveOpen
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme.{u}} (p q : D ⟶ A) (w : A ⟶ T)
  (h : p ≫ w = q ≫ w) [Etale p] [Mono (pullback.lift p q h)]
  [LocallyOfFinitePresentation w]
local notation "U" => targetOpen p q w h
local notation "π" => projection p q w h

/-- Every represented point constructs a genuine open branch in the unrestricted source. -/
theorem exists_open_source_branch_of_fppfLocus
    (hn : (SchemeFppfTargetOpen.locus π : Set (U).toScheme).Nonempty) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ A),
      IsOpenImmersion a ∧ Etale (a ≫ w) ∧ Nonempty Z := by
  let C := SchemeFppfTargetOpen.source π
  let e : C ⟶ source p q w h := pullback.fst π (SchemeFlatTargetOpen.locus π).ι
  let a : C ⟶ A := e ≫ pullback.fst w (U).ι
  let j := SchemeFppfTargetOpen.projection π
  let _ : Etale j := fppfProjection_etale p q w h
  have he : a ≫ w = j ≫ (SchemeFppfTargetOpen.locus π).ι ≫ (U).ι := by
    change (e ≫ pullback.fst w (U).ι) ≫ w = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (e ≫ π) ≫ (U).ι = _
    rw [(SchemeFppfTargetOpen.isPullback π).w, Category.assoc]
  refine ⟨C, a, inferInstanceAs (IsOpenImmersion (e ≫ pullback.fst w (U).ι)), ?_, ?_⟩
  · rw [he]
    infer_instance
  · obtain ⟨y, hy⟩ := hn
    obtain ⟨z, _⟩ := j.surjective ⟨y, hy⟩
    exact ⟨z⟩

variable [Etale q] [IsNoetherian A] [IsNoetherian T] [QuasiCompact w] [IrreducibleSpace T]
local notation "m" => pullback.lift p q h
local notation "v" => pullback.fst w w ≫ w

/-- Point coverage plus one open etale source branch is exactly the missing generic condition. -/
theorem fppfLocus_nonempty_iff_generic_image_and_open_branch :
    (SchemeFppfTargetOpen.locus π : Set (U).toScheme).Nonempty ↔
      (∀ x : (pullback w w : Scheme), v x = genericPoint T → x ∈ Set.range m) ∧
      ∃ (Z : Scheme.{u}) (a : Z ⟶ A),
        IsOpenImmersion a ∧ Etale (a ≫ w) ∧ Nonempty Z := by
  constructor
  · intro hn
    refine ⟨?_, exists_open_source_branch_of_fppfLocus p q w h hn⟩
    obtain ⟨y, _⟩ := hn
    have hg := (targetOpen_nonempty_iff_genericFiber p q w h).mp ⟨y.val, y.property⟩
    intro x hx
    exact MonomorphismOpenImage.locus_subset_range m (hg x hx)
  · rintro ⟨hg, Z, a, ha, ht, hn⟩
    let _ := ha
    let _ := ht
    let _ := hn
    exact fppfLocus_nonempty_of_source_branch p q w h a hg

end FLT.Mazur.KernelPairEffectiveOpen

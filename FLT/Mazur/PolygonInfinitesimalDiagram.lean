/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicAtlas
public import FLT.Mazur.PolygonSmoothingNilpotentBranches

/-!
# The cyclic diagram of infinitesimal smoothing charts

For a nilpotent smoothing parameter, actual arithmetic node charts and Laurent
edges form a locally directed diagram of open immersions. Its scheme colimit
therefore has the full gluing cocycle supplied by Mathlib's gluing theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing
open PolygonCyclicAtlas (shape)

variable (R : Type u) [CommRing R] (t : R) (n : ℕ)

/-- The actual punctured branches used in the cyclic gluing. -/
def index : MultispanIndex (shape n) Scheme where
  left _ := branchTorus R
  right _ := PolygonSmoothing.chart R t
  fst _ := leftBranchOpen R t
  snd _ := precedingBranch R t

/-- The cyclic diagram of node charts and Laurent edges. -/
def diagram : WalkingMultispan (shape n) ⥤ Scheme := (index R t n).multispan

instance map_isOpenImmersion {i j : WalkingMultispan (shape n)} (f : i ⟶ j) :
    IsOpenImmersion ((diagram R t n).map f) := by
  cases f with
  | id i => change IsOpenImmersion (𝟙 _); infer_instance
  | fst i => exact leftBranchOpen_isOpenImmersion R t
  | snd i =>
    change IsOpenImmersion (precedingBranch R t)
    infer_instance

variable [Fact (IsNilpotent t)]

instance diagram_locallyDirected : ((diagram R t n) ⋙ Scheme.forget).IsLocallyDirected := by
  have aux : ∀ {i j k k' : WalkingMultispan (shape n)} (fi : i ⟶ k) (fj : j ⟶ k')
      (xi : (diagram R t n ⋙ Scheme.forget).obj i)
      (xj : (diagram R t n ⋙ Scheme.forget).obj j), k = k' →
      HEq ((diagram R t n ⋙ Scheme.forget).map fi xi)
        ((diagram R t n ⋙ Scheme.forget).map fj xj) →
      ∃ (l : WalkingMultispan (shape n)) (fli : l ⟶ i) (flj : l ⟶ j)
        (x : (diagram R t n ⋙ Scheme.forget).obj l),
        (diagram R t n ⋙ Scheme.forget).map fli x = xi ∧
        (diagram R t n ⋙ Scheme.forget).map flj x = xj := by
    intro i j k k' fi fj
    cases fi with
    | id i =>
      intro xi xj hk he
      subst k'
      exact ⟨j, fj, 𝟙 _, xj, (eq_of_heq he).symm, rfl⟩
    | fst a =>
      cases fj with
      | id j =>
        intro xi xj hk he
        subst j
        exact ⟨_, 𝟙 _, .fst a, xi, rfl, eq_of_heq he⟩
      | fst b =>
        intro xi xj hk he
        have hab : a = b := WalkingMultispan.right.inj hk
        subst b
        have hx := (leftBranchOpen R t).isOpenEmbedding.injective (eq_of_heq he)
        exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, hx⟩
      | snd b =>
        intro xi xj hk he
        exact False.elim ((Set.disjoint_left.mp
          (branchOpen_nilpotent_disjoint R t (Fact.out : IsNilpotent t)))
          ⟨xi, rfl⟩ ⟨(edgeInversion R).hom xj, (eq_of_heq he).symm⟩)
    | snd a =>
      cases fj with
      | id j =>
        intro xi xj hk he
        subst j
        exact ⟨_, 𝟙 _, .snd a, xi, rfl, eq_of_heq he⟩
      | fst b =>
        intro xi xj hk he
        exact False.elim ((Set.disjoint_left.mp
          (branchOpen_nilpotent_disjoint R t (Fact.out : IsNilpotent t)))
          ⟨xj, eq_of_heq he |>.symm⟩ ⟨(edgeInversion R).hom xi, rfl⟩)
      | snd b =>
        intro xi xj hk he
        have hab : a = b := (finRotate n).symm.injective (WalkingMultispan.right.inj hk)
        subst b
        have hx := ((edgeInversion R).hom ≫
          rightBranchOpen R t).isOpenEmbedding.injective (eq_of_heq he)
        exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, hx⟩
  exact ⟨fun fi fj xi xj he ↦ aux fi fj xi xj rfl (heq_of_eq he)⟩


end FLT.Mazur.PolygonInfinitesimal

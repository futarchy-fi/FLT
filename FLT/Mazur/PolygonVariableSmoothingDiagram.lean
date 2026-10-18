/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonCyclicAtlas
public import FLT.Mazur.PolygonSmoothingNilpotentBranches

/-!
# Cyclic gluing with a separate smoothing at each node

All edges use the full Laurent coordinate. Nilpotence is required separately
at each node and gives disjoint branches without equating smoothing parameters.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonVariableSmoothing

open PolygonSmoothing
open PolygonCyclicAtlas (shape)

variable (R : Type u) [CommRing R] (n : ℕ) (t : Fin n → R)

/-- The actual punctured branches used in the cyclic gluing. -/
def index : MultispanIndex (shape n) Scheme where
  left _ := branchTorus R
  right i := PolygonSmoothing.chart R (t i)
  fst i := leftBranchOpen R (t i)
  snd i := precedingBranch R (t ((finRotate n).symm i))

/-- The cyclic diagram of node charts and Laurent edges. -/
def diagram : WalkingMultispan (shape n) ⥤ Scheme := (index R n t).multispan

instance map_isOpenImmersion {i j : WalkingMultispan (shape n)} (f : i ⟶ j) :
    IsOpenImmersion ((diagram R n t).map f) := by
  cases f with
  | id i => change IsOpenImmersion (𝟙 _); infer_instance
  | fst i => exact leftBranchOpen_isOpenImmersion R (t i)
  | snd i =>
    change IsOpenImmersion (precedingBranch R (t ((finRotate n).symm i)))
    infer_instance

variable [∀ i, Fact (IsNilpotent (t i))]

instance diagram_locallyDirected : ((diagram R n t) ⋙ Scheme.forget).IsLocallyDirected := by
  have aux : ∀ {i j k k' : WalkingMultispan (shape n)} (fi : i ⟶ k) (fj : j ⟶ k')
      (xi : (diagram R n t ⋙ Scheme.forget).obj i)
      (xj : (diagram R n t ⋙ Scheme.forget).obj j), k = k' →
      HEq ((diagram R n t ⋙ Scheme.forget).map fi xi)
        ((diagram R n t ⋙ Scheme.forget).map fj xj) →
      ∃ (l : WalkingMultispan (shape n)) (fli : l ⟶ i) (flj : l ⟶ j)
        (x : (diagram R n t ⋙ Scheme.forget).obj l),
        (diagram R n t ⋙ Scheme.forget).map fli x = xi ∧
        (diagram R n t ⋙ Scheme.forget).map flj x = xj := by
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
        have hx := (leftBranchOpen R (t a)).isOpenEmbedding.injective (eq_of_heq he)
        exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, hx⟩
      | snd b =>
        intro xi xj hk he
        have hab : a = (finRotate n).symm b := WalkingMultispan.right.inj hk
        subst a
        exact False.elim ((Set.disjoint_left.mp
          (branchOpen_nilpotent_disjoint R _ (Fact.out : IsNilpotent _)))
          ⟨xi, rfl⟩ ⟨(edgeInversion R).hom xj, (eq_of_heq he).symm⟩)
    | snd a =>
      cases fj with
      | id j =>
        intro xi xj hk he
        subst j
        exact ⟨_, 𝟙 _, .snd a, xi, rfl, eq_of_heq he⟩
      | fst b =>
        intro xi xj hk he
        have hab : (finRotate n).symm a = b := WalkingMultispan.right.inj hk
        subst b
        exact False.elim ((Set.disjoint_left.mp
          (branchOpen_nilpotent_disjoint R _ (Fact.out : IsNilpotent _)))
          ⟨xj, eq_of_heq he |>.symm⟩ ⟨(edgeInversion R).hom xi, rfl⟩)
      | snd b =>
        intro xi xj hk he
        have hab : a = b := (finRotate n).symm.injective (WalkingMultispan.right.inj hk)
        subst b
        have hx := ((edgeInversion R).hom ≫
          rightBranchOpen R (t ((finRotate n).symm a))).isOpenEmbedding.injective (eq_of_heq he)
        exact ⟨_, 𝟙 _, 𝟙 _, xi, rfl, hx⟩
  exact ⟨fun fi fj xi xj he ↦ aux fi fj xi xj rfl (heq_of_eq he)⟩


end FLT.Mazur.PolygonVariableSmoothing

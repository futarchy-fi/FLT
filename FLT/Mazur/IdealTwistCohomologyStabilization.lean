/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTwistTransitionExact
public import FLT.Mazur.ProperCoherentCohomology
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Stabilization of positive ideal-twist cohomology

Surjectivity and proper coherent finiteness make the cohomology systems
eventually constant up to isomorphism. Vanishing of that stable value still
requires the finite-stage annihilation argument.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

universe u v

/-- Surjective successor maps imply surjectivity of every map in a sequential system. -/
theorem sequence_map_surjective {k : Type u} [Ring k] (F : ℕ ⥤ ModuleCat.{v} k)
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1))))
    {n m : ℕ} (h : n ≤ m) : Function.Surjective (F.map (homOfLE h)) := by
  induction m, h using Nat.le_induction with
  | base => simpa using (Function.surjective_id : Function.Surjective (id : F.obj n → F.obj n))
  | succ m h ih =>
    have he : homOfLE (show n ≤ m + 1 from h.trans (Nat.le_add_right m 1)) =
        homOfLE h ≫ homOfLE (Nat.le_add_right m 1) := rfl
    rw [he, F.map_comp]
    exact (hF m).comp ih

/-- A surjective sequence of finite-dimensional vector spaces eventually has only isomorphisms. -/
theorem sequence_eventually_isIso {k : Type u} [Field k] (F : ℕ ⥤ ModuleCat.{v} k)
    [∀ n, Module.Finite k (F.obj n)]
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)))) :
    ∃ n : ℕ, ∀ m : ℕ, ∀ h : n ≤ m, IsIso (F.map (homOfLE h)) := by
  classical
  let d (n : ℕ) := Module.finrank k (F.obj n)
  have hex : ∃ r : ℕ, ∃ n : ℕ, d n = r := ⟨d 0, 0, rfl⟩
  obtain ⟨n, hn⟩ := Nat.find_spec hex
  refine ⟨n, fun m h ↦ ?_⟩
  have hdim : d n ≤ d m := by
    rw [hn]
    exact Nat.find_min' hex ⟨m, rfl⟩
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact OrzechProperty.bijective_of_surjective_of_finrank_le
    (F.map (homOfLE h)).hom (sequence_map_surjective F hF h) hdim

namespace LineSectionTwistSystem

open ModuleSheafTensor ModuleLineBundleTensorPullback
open FLT.Mazur.GlobalIdealPower FLT.Mazur.CoherentIdealIntersection

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- Positive cohomology of any ideal twist stabilizes along a nonzero section. -/
theorem idealCohomology_eventually_isIso (hd : topologicalKrullDim X ≤ 1)
    (I : X.IdealSheafData) {L : X.Modules} (hL : LocallyFreeRankOne L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (q : ℕ) (hq : 0 < q) :
    ∃ n : ℕ, ∀ m : ℕ, ∀ h : n ≤ m,
      IsIso ((idealCohomology f s I q).map (homOfLE h)) := by
  have := Chow.source_isNoetherian f
  have := idealModule_coherent I
  have hfin (n : ℕ) : Module.Finite k ((idealCohomology f s I q).obj n) := by
    have := (hL.tensorPower n).isFinitePresentation
    have := tensor_coherent (idealModule I) (tensorPower L n)
    exact proper_coherent_hasFiniteCohomology f
      (tensor (idealModule I) (tensorPower L n)) q
  let := hfin
  apply sequence_eventually_isIso
  intro n
  change Function.Surjective ((cohomology f (idealModule I) s q).map
    (homOfLE (Nat.le_add_right n 1)))
  rw [cohomology_map_succ]
  exact idealStep_cohomology_surjective f hd I hL s hs n q hq

end LineSectionTwistSystem
end FLT.Mazur.FCurve

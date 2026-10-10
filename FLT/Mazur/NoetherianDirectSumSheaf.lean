/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCoverDirectSumSheaf
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Pointwise sums on a Noetherian space

Every open in a Noetherian space is compact. Hence every covering sieve
has a finite covering subfamily, and the pointwise sum satisfies descent.
The Noetherian hypothesis is essential to this argument for arbitrary opens.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open FLT.Mazur.FiniteCoverDirectSum

universe u

namespace FLT.Mazur.NoetherianDirectSum

variable (X : Type u) [TopologicalSpace X] [NoetherianSpace X]

/-- Each covering sieve of opens has a finite covering subfamily. -/
lemma exists_finite_subcover (U : Opens X) (S : Sieve U)
    (hS : S ∈ Opens.grothendieckTopology X U) :
    ∃ s : Finset (CoverArrow S),
      Sieve.generate (finitePresieve s) ∈ Opens.grothendieckTopology X U := by
  classical
  have hcover : (U : Set X) ⊆ ⋃ i : CoverArrow S, (i.1 : Set X) := by
    intro x hx
    obtain ⟨V, f, hf, hxV⟩ := hS x hx
    exact Set.mem_iUnion.mpr ⟨⟨V, f, hf⟩, hxV⟩
  obtain ⟨s, hs⟩ := (NoetherianSpace.isCompact (U : Set X)).elim_finite_subcover
    (fun i : CoverArrow S ↦ (i.1 : Set X)) (fun i ↦ i.1.isOpen) hcover
  refine ⟨s, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact ⟨i.1, i.2.val, Sieve.le_generate _ _ _
    (Presieve.ofArrows.mk (⟨i, hi⟩ : s)), hxi⟩

/-- Actual pointwise sums of abelian sheaves on a Noetherian space are sheaves. -/
lemma isSheaf (P : ℕ → (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ n, Presheaf.IsSheaf (Opens.grothendieckTopology X) (P n)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (FiniteCoverDirectSum.presheaf P) :=
  FiniteCoverDirectSum.isSheaf _ (exists_finite_subcover X) P hP

end FLT.Mazur.NoetherianDirectSum

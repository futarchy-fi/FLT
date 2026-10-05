/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisSheafExtension
public import FLT.Mazur.FiniteCoverDirectSumSheaf

/-!
# Finite subcovers on the affine site

Compactness of an affine open extracts finitely many arrows from each
covering sieve. This supplies the finite-support hypothesis for direct sums.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.FiniteCoverDirectSum

universe u

namespace FLT.Mazur.AffineBasis

variable (X : Scheme.{u})

/-- Every covering sieve on an affine open admits a finite covering subfamily. -/
lemma exists_finite_subcover (U : X.affineOpens) (S : Sieve U)
    (hS : S ∈ topology X U) :
    ∃ s : Finset (CoverArrow S), Sieve.generate (finitePresieve s) ∈ topology X U := by
  classical
  have hcover : (U.1 : Set X) ⊆ ⋃ i : CoverArrow S, (i.1.1 : Set X) := by
    intro x hx
    obtain ⟨V, f, hf, hxV⟩ :=
      ((inclusion X).mem_inducedTopology_iff_of_isCoverDense _ S).mp hS x hx
    obtain ⟨W, g, h, hg, _⟩ := hf
    exact Set.mem_iUnion.mpr ⟨⟨W, g, hg⟩, h.le hxV⟩
  obtain ⟨s, hs⟩ := U.2.isCompact.elim_finite_subcover
    (fun i : CoverArrow S ↦ (i.1.1 : Set X)) (fun i ↦ i.1.1.isOpen) hcover
  refine ⟨s, ((inclusion X).mem_inducedTopology_iff_of_isCoverDense _ _).mpr ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
  refine ⟨i.1.1, (inclusion X).map i.2.val, ?_, hxi⟩
  exact ⟨i.1, i.2.val, 𝟙 _, Sieve.le_generate _ _ _
    (Presieve.ofArrows.mk (⟨i, hi⟩ : s)), (Category.id_comp _).symm⟩

/-- Pointwise direct sums of sheaves on the affine basis satisfy descent. -/
lemma directSum_isSheaf (P : ℕ → X.affineOpensᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ n, Presheaf.IsSheaf (topology X) (P n)) :
    Presheaf.IsSheaf (topology X) (FiniteCoverDirectSum.presheaf P) :=
  FiniteCoverDirectSum.isSheaf (topology X) (exists_finite_subcover X) P hP

end FLT.Mazur.AffineBasis

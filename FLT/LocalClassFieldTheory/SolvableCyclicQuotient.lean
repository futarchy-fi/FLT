/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.SolvableNormalStep
public import Mathlib.GroupTheory.QuotientGroup.Simple
public import Mathlib.Order.Atoms.Finite

/-!
# A cyclic quotient for solvable induction

A maximal subgroup of the nontrivial finite abelianization gives a cyclic
quotient. Its kernel is a proper normal subgroup of the original group.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

/-- A nontrivial finite solvable group has a cyclic quotient by a proper normal subgroup. -/
theorem solvable_cyclic_quotient (G : Type) [Group G] [Finite G]
    [Group.IsSolvable G] [Nontrivial G] :
    ∃ (N : Subgroup G) (hN : N.Normal), letI := hN; N ≠ ⊤ ∧ IsCyclic (G ⧸ N) := by
  classical
  have hc : commutator G ≠ ⊤ := (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne
  let : Nontrivial (Abelianization G) := QuotientGroup.nontrivial_iff.mpr hc
  let : Finite (Abelianization G) := inferInstanceAs (Finite (G ⧸ commutator G))
  let : Finite (Subgroup (Abelianization G)) :=
    Finite.of_injective (fun H : Subgroup (Abelianization G) => (H : Set (Abelianization G)))
      SetLike.coe_injective
  obtain ⟨P, hP, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (Abelianization G))).resolve_left
    bot_ne_top
  let : IsSimpleGroup (Abelianization G ⧸ P) := CommGroup.isSimpleGroup_iff_isCoatom.mpr hP
  let f : G →* Abelianization G ⧸ P := (QuotientGroup.mk' P).comp Abelianization.of
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective P).comp (QuotientGroup.mk'_surjective (commutator G))
  refine ⟨f.ker, inferInstance, ?_, ?_⟩
  · intro he
    obtain ⟨q, hq⟩ := exists_ne (1 : Abelianization G ⧸ P)
    obtain ⟨g, rfl⟩ := hf q
    exact hq (show g ∈ f.ker from he ▸ Subgroup.mem_top g)
  · exact (QuotientGroup.quotientKerEquivOfSurjective f hf).isCyclic.mpr inferInstance

end LocalClassFieldTheory

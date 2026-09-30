/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.CyclicScalarRestriction
public import FLT.Deformations.RepresentationTheory.ThreeStableLines

/-!
# Exactly two stable lines for a reducible cyclic restriction

A third stable line would force scalar subgroup action and hence a stable
line for the whole group, contradicting irreducibility. The complementary
pair supplied by reducible restriction therefore exhausts the stable lines.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V) (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)]

/-- An irreducible rank-two representation with reducible restriction to a
normal subgroup with cyclic quotient has exactly two stable lines, in one orbit. -/
theorem exists_stableLines_pair_of_cyclic_quotient
    (hV : Module.finrank k V = 2) (hirr : ρ.IsIrreducible)
    (hres : ¬ Representation.IsIrreducible (ρ.comp H.subtype)) :
    ∃ L M : Submodule k V, L ≠ M ∧ IsCompl L M ∧
      ρ.stableLines H = {L, M} ∧ ∃ g : G, L.map (ρ g) = M := by
  classical
  obtain ⟨L, M, hL, hM, hne, hc, hmoved⟩ :=
    ρ.exists_complementary_stableLines H hV hirr hres
  refine ⟨L, M, hne, hc, ?_, hmoved⟩
  ext N
  constructor
  · intro hN
    by_cases hLN : L = N
    · simp [← hLN]
    by_cases hMN : M = N
    · simp [← hMN]
    exfalso
    apply ρ.not_isIrreducible_of_scalar_restriction H hV _ hirr
    intro h
    exact (ρ h).exists_scalar_of_three_lines hV hL.1 hM.1 hN.1 hne hLN hMN
      (by rintro v ⟨w, hw, rfl⟩; exact hL.2 h w hw)
      (by rintro v ⟨w, hw, rfl⟩; exact hM.2 h w hw)
      (by rintro v ⟨w, hw, rfl⟩; exact hN.2 h w hw)
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact hL
    · exact Set.mem_singleton_iff.mp hN ▸ hM

end Representation

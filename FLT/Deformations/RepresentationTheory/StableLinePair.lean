/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Complementary stable lines in rank two

Normality transports stable lines. An irreducible rank-two representation
with reducible restriction therefore has two complementary stable lines,
one a translate of the other. This does not yet assert that these are the
only stable lines, even when the quotient is cyclic.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (H : Subgroup G)

/-- The one-dimensional subspaces stable under a subgroup. -/
def stableLines : Set (Submodule k V) :=
  {L | Module.finrank k L = 1 ∧ ∀ h : H, ∀ v ∈ L, ρ h v ∈ L}

/-- Normality transports stable lines by every group element. -/
theorem map_mem_stableLines [H.Normal] {L : Submodule k V}
    (hL : L ∈ ρ.stableLines H) (g : G) : L.map (ρ g) ∈ ρ.stableLines H := by
  constructor
  · exact (LinearEquiv.finrank_map_eq
      (LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)) L).trans hL.1
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨ρ (g⁻¹ * h * g) w,
      hL.2 ⟨_, Subgroup.Normal.conj_mem' (inferInstance : H.Normal) (h : G) h.property g⟩ w hw, ?_⟩
    simp [map_mul, Module.End.mul_apply]

variable [FiniteDimensional k V]

/-- Distinct lines in a two-dimensional space are complementary. -/
theorem isCompl_of_distinct_lines (hV : Module.finrank k V = 2)
    {L M : Submodule k V} (hL : Module.finrank k L = 1)
    (hM : Module.finrank k M = 1) (hne : L ≠ M) : IsCompl L M := by
  apply (Submodule.isCompl_iff_disjoint L M (by omega)).2
  exact (Submodule.isAtom_iff_finrank_eq_one.mpr hL).disjoint_of_ne
    (Submodule.isAtom_iff_finrank_eq_one.mpr hM) hne

/-- A proper nonzero subrepresentation of a rank-two space is a line. -/
theorem exists_stableLine_of_reducible (hV : Module.finrank k V = 2)
    (hres : ¬ Representation.IsIrreducible (ρ.comp H.subtype)) :
    ∃ L, L ∈ ρ.stableLines H := by
  classical
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank k V)
  have hntS : Nontrivial (Subrepresentation (ρ.comp H.subtype)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have ht : (⊥ : Submodule k V) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top ht
  have hex : ∃ L : Subrepresentation (ρ.comp H.subtype), L ≠ ⊥ ∧ L ≠ ⊤ := by
    by_contra! hn
    exact hres { eq_bot_or_eq_top := fun L ↦ or_iff_not_imp_left.mpr (hn L) }
  obtain ⟨L, hbot, htop⟩ := hex
  have hb : L.toSubmodule ≠ ⊥ := fun h ↦ hbot (Subrepresentation.toSubmodule_injective h)
  have ht : L.toSubmodule ≠ ⊤ := fun h ↦ htop (Subrepresentation.toSubmodule_injective h)
  refine ⟨L.toSubmodule, ?_, fun h v hv ↦ L.apply_mem_toSubmodule h hv⟩
  have hpos : Module.finrank k L.toSubmodule ≠ 0 := by
    exact fun hz ↦ hb (Submodule.finrank_eq_zero.mp hz)
  have hlt := Submodule.finrank_lt ht
  omega

omit [FiniteDimensional k V] in
/-- An irreducible rank-two representation moves every line. -/
theorem exists_map_line_ne (hV : Module.finrank k V = 2)
    (hirr : ρ.IsIrreducible) {L : Submodule k V} (hL : Module.finrank k L = 1) :
    ∃ g : G, L.map (ρ g) ≠ L := by
  classical
  by_contra! h
  let S : Subrepresentation ρ := ⟨L, fun g v hv ↦ by
    rw [← h g]
    exact ⟨v, hv, rfl⟩⟩
  let := hirr
  rcases eq_bot_or_eq_top S with hs | hs
  · have he : L = ⊥ := congrArg Subrepresentation.toSubmodule hs
    rw [he, finrank_bot] at hL
    omega
  · have he : L = ⊤ := congrArg Subrepresentation.toSubmodule hs
    rw [he, finrank_top, hV] at hL
    omega

/-- Reducible restriction to a normal subgroup supplies a complementary
pair of stable lines in a single orbit. It need not exhaust that orbit. -/
theorem exists_complementary_stableLines [H.Normal] (hV : Module.finrank k V = 2)
    (hirr : ρ.IsIrreducible)
    (hres : ¬ Representation.IsIrreducible (ρ.comp H.subtype)) :
    ∃ L M : Submodule k V, L ∈ ρ.stableLines H ∧ M ∈ ρ.stableLines H ∧
      L ≠ M ∧ IsCompl L M ∧ ∃ g : G, L.map (ρ g) = M := by
  obtain ⟨L, hL⟩ := ρ.exists_stableLine_of_reducible H hV hres
  obtain ⟨g, hg⟩ := ρ.exists_map_line_ne hV hirr hL.1
  have hM := ρ.map_mem_stableLines H hL g
  exact ⟨L, L.map (ρ g), hL, hM, hg.symm,
    isCompl_of_distinct_lines hV hL.1 hM.1 hg.symm, g, rfl⟩


omit [FiniteDimensional k V] in
/-- If two lines exhaust the stable lines, every group element preserves or
swaps the pair. Normality supplies stability of both images. -/
theorem permutes_stableLine_pair [H.Normal] {L M : Submodule k V}
    (hne : L ≠ M) (hpair : ρ.stableLines H = {L, M}) (g : G) :
    (L.map (ρ g) = L ∧ M.map (ρ g) = M) ∨
      (L.map (ρ g) = M ∧ M.map (ρ g) = L) := by
  have hL : L ∈ ρ.stableLines H := by rw [hpair]; simp
  have hM : M ∈ ρ.stableLines H := by rw [hpair]; simp
  have hLi := ρ.map_mem_stableLines H hL g
  have hMi := ρ.map_mem_stableLines H hM g
  rw [hpair, Set.mem_insert_iff, Set.mem_singleton_iff] at hLi hMi
  have hi : L.map (ρ g) ≠ M.map (ρ g) :=
    fun he ↦ hne (Submodule.map_injective_of_injective (ρ.apply_bijective g).1 he)
  aesop

omit [FiniteDimensional k V] in
/-- Elements of the subgroup fix its stable lines. -/
theorem map_stableLine_subgroup {L : Submodule k V} (hL : L ∈ ρ.stableLines H)
    (h : H) : L.map (ρ (h : G)) = L := by
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    exact hL.2 h w hw
  · intro v hv
    exact ⟨ρ (h⁻¹ : H) v, hL.2 h⁻¹ v hv, ρ.self_inv_apply h v⟩

end Representation

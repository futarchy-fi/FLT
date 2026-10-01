/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.StableLinePair
public import Mathlib.LinearAlgebra.Projection

/-!
# Three stable lines force a scalar endomorphism

In dimension two, a third line distinct from two complementary lines has
nonzero components in both. Invariance forces the two scalar actions to agree.
-/

@[expose] public section

namespace LinearMap

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- An endomorphism preserving a line acts on it by a scalar. -/
theorem exists_scalar_on_line (f : V →ₗ[k] V) {L : Submodule k V}
    (hL : Module.finrank k L = 1) (hf : L.map f ≤ L) :
    ∃ a : k, ∀ v ∈ L, f v = a • v := by
  obtain ⟨v, hv, hspan⟩ := (finrank_eq_one_iff').mp hL
  obtain ⟨a, ha⟩ := hspan ⟨f v, hf ⟨v, v.property, rfl⟩⟩
  refine ⟨a, fun w hw ↦ ?_⟩
  obtain ⟨b, hb⟩ := hspan ⟨w, hw⟩
  have ha' : a • (v : V) = f v := congrArg Subtype.val ha
  have hb' : b • (v : V) = w := congrArg Subtype.val hb
  rw [← hb', map_smul, ← ha', smul_comm]

variable [FiniteDimensional k V]

/-- Preserving three distinct lines in dimension two forces scalar action. -/
theorem exists_scalar_of_three_lines (f : V →ₗ[k] V)
    (hV : Module.finrank k V = 2) {L M N : Submodule k V}
    (hL : Module.finrank k L = 1) (hM : Module.finrank k M = 1)
    (hN : Module.finrank k N = 1) (hLM : L ≠ M) (hLN : L ≠ N) (hMN : M ≠ N)
    (hfL : L.map f ≤ L) (hfM : M.map f ≤ M) (hfN : N.map f ≤ N) :
    ∃ a : k, f = a • LinearMap.id := by
  obtain ⟨a, ha⟩ := f.exists_scalar_on_line hL hfL
  obtain ⟨b, hb⟩ := f.exists_scalar_on_line hM hfM
  obtain ⟨c, hc⟩ := f.exists_scalar_on_line hN hfN
  have hcompl := Representation.isCompl_of_distinct_lines hV hL hM hLM
  obtain ⟨z, hz, _⟩ := (finrank_eq_one_iff').mp hN
  have hz0 : (z : V) ≠ 0 := fun h ↦ hz (Subtype.ext h)
  obtain ⟨x, y, hxy, huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl (z : V)
  have hx0 : (x : V) ≠ 0 := by
    intro hx
    have hzy : (z : V) = y := by simpa [hx] using hxy.symm
    apply hMN
    exact (eq_span_singleton_of_mem_of_finrank_eq_one hM
      (hzy ▸ y.property) hz0).trans
      (eq_span_singleton_of_mem_of_finrank_eq_one hN z.property hz0).symm
  have hy0 : (y : V) ≠ 0 := by
    intro hy
    have hzx : (z : V) = x := by simpa [hy] using hxy.symm
    apply hLN
    exact (eq_span_singleton_of_mem_of_finrank_eq_one hL
      (hzx ▸ x.property) hz0).trans
      (eq_span_singleton_of_mem_of_finrank_eq_one hN z.property hz0).symm
  have he : a • (x : V) + b • (y : V) = c • (x : V) + c • (y : V) := by
    rw [← ha _ x.property, ← hb _ y.property, ← map_add, hxy,
      hc _ z.property, ← smul_add, hxy]
  have hu := (Submodule.existsUnique_add_of_isCompl hcompl
    (a • (x : V) + b • (y : V)))
  obtain ⟨u, v, huv, huvuniq⟩ := hu
  have hab := huvuniq (a • x) (b • y) rfl
  have hcc := huvuniq (c • x) (c • y) he.symm
  have hac : a = c := (smul_left_injective k hx0)
    (congrArg Subtype.val (hab.1.trans hcc.1.symm))
  have hbc : b = c := (smul_left_injective k hy0)
    (congrArg Subtype.val (hab.2.trans hcc.2.symm))
  refine ⟨c, ?_⟩
  ext w
  obtain ⟨u, v, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl hcompl w
  simp [map_add, ha _ u.property, hb _ v.property, hac, hbc]

end LinearMap

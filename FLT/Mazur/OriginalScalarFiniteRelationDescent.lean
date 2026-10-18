/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalScalarFiniteLinearLifts
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Clearing finitely generated relations before linear descent

If each residual relation is killed by an original prime denominator, finite
generation supplies one denominator killing all relations. The rescaled
numerator map then descends to the presented boundary module. Boundary-zero
alone is insufficient: actual scalar annihilation is an explicit hypothesis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OriginalScalarFiniteRelationDescent
variable {R E A B : Type*} [CommRing R] [AddCommGroup E] [AddCommGroup A]
  [AddCommGroup B] [Module R E] [Module R A] [Module R B]
  (P : Ideal R) [P.IsPrime] (K : Submodule R E) (L : E →ₗ[R] A)

/-- Finite generation upgrades individual denominator annihilation to one uniform scalar. -/
theorem exists_scalar_killing_relations (hK : K.FG)
    (h : ∀ c ∈ K, ∃ r : R, r ∉ P ∧ r • L c = 0) :
    ∃ r : R, r ∉ P ∧ K ≤ LinearMap.ker (r • L) := by
  obtain ⟨n, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  have hmem (j : Fin n) : t j ∈ K := ht ▸ Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨r, hr, w, hw⟩ := OriginalScalarFiniteLinearLifts.exists_common
    (⊥ : Submodule R A) LinearMap.id P (fun j ↦ L (t j)) (fun j ↦ by
      obtain ⟨s, hs, he⟩ := h (t j) (hmem j)
      exact ⟨s, hs, 0, he.symm⟩)
  refine ⟨r, hr, ?_⟩
  rw [← ht, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change r • L (t j) = 0
  have hz : (w j).val = 0 := (w j).property
  exact (hw j).symm.trans hz

/-- The uniform scalar constructs a genuine map from the quotient by all relations. -/
theorem exists_quotient_lift (hK : K.FG)
    (h : ∀ c ∈ K, ∃ r : R, r ∉ P ∧ r • L c = 0) :
    ∃ r : R, r ∉ P ∧ ∃ D : (E ⧸ K) →ₗ[R] A,
      D.comp K.mkQ = r • L := by
  obtain ⟨r, hr, hk⟩ := exists_scalar_killing_relations P K L hK h
  exact ⟨r, hr, K.liftQ (r • L) hk, K.liftQ_mkQ (r • L) hk⟩

/-- Descent keeps the original scaled boundary, with only a further original denominator. -/
theorem exists_quotient_boundary_lift (β : A →ₗ[R] B) (T : E →ₗ[R] B)
    (hT : K ≤ LinearMap.ker T) (x : R) (hx : x ∉ P)
    (hL : β.comp L = x • T) (hK : K.FG)
    (h : ∀ c ∈ K, ∃ r : R, r ∉ P ∧ r • L c = 0) :
    ∃ y : R, y ∉ P ∧ ∃ D : (E ⧸ K) →ₗ[R] A,
      β.comp D = y • K.liftQ T hT := by
  obtain ⟨r, hr, D, hD⟩ := exists_quotient_lift P K L hK h
  refine ⟨r * x, P.primeCompl.mul_mem hr hx, D, ?_⟩
  apply LinearMap.ext
  intro c
  induction c using Submodule.Quotient.induction_on with
  | _ c =>
    change β (D (K.mkQ c)) = (r * x) • T c
    have hd := LinearMap.congr_fun hD c
    change D (K.mkQ c) = r • L c at hd
    rw [hd, map_smul]
    have hb := LinearMap.congr_fun hL c
    change β (L c) = x • T c at hb
    rw [hb, smul_smul]

end FLT.Mazur.OriginalScalarFiniteRelationDescent

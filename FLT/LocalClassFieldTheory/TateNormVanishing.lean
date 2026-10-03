/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateClassArithmetic

/-!
# Vanishing at the norm splice

Degree-zero Tate vanishing is exactly norm surjectivity on invariants. Degree
minus one vanishes exactly when every norm-zero element is an augmentation boundary.
Both criteria refer to the differentials of the actual Tate complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- Tate degree-zero vanishing makes the norm surjective on invariant elements. -/
theorem norm_surjective_of_tate_zero (h : Limits.IsZero (tateCohomology M 0))
    (x : M) (hx : d₀₁ M x = 0) : ∃ y : M, M.norm.hom y = x := by
  let z := (cochainsIso₀ M).inv x
  have hz : (tateComplex M).d 0 (0 + 1) z = 0 := by
    change (tateComplex M).d 0 1 z = 0
    apply (ModuleCat.mono_iff_injective (cochainsIso₁ M).hom).mp inferInstance
    have hd := congrArg (fun f => f.hom z) (comp_d₀₁_eq M)
    change d₀₁ M ((cochainsIso₀ M).hom z) =
      (cochainsIso₁ M).hom ((tateComplex M).d 0 1 z) at hd
    simpa only [z, Iso.inv_hom_id_apply, hx, map_zero] using hd.symm
  have := ModuleCat.isZero_iff_subsingleton.mp h
  obtain ⟨b, hb⟩ := (tateCocycleClass_eq_zero_iff M 0 z hz).mp (Subsingleton.elim _ _)
  refine ⟨(chainsIso₀ M).hom b, ?_⟩
  have he := congrArg (cochainsIso₀ M).hom hb
  change (cochainsIso₀ M).hom ((cochainsIso₀ M).inv
    (M.norm.hom ((chainsIso₀ M).hom b))) = (cochainsIso₀ M).hom ((cochainsIso₀ M).inv x) at he
  simpa only [Iso.inv_hom_id_apply] using he

/-- Norm surjectivity on invariants kills Tate degree zero. -/
theorem tate_zero_isZero_of_norm_surjective
    (h : ∀ x : M, d₀₁ M x = 0 → ∃ y : M, M.norm.hom y = x) :
    Limits.IsZero (tateCohomology M 0) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices hz : ∀ a : tateCohomology M 0, a = 0 from ⟨fun a b => (hz a).trans (hz b).symm⟩
  intro a
  obtain ⟨z, hz, rfl⟩ := tateCocycleClass_surjective M 0 a
  change (tateComplex M).d 0 1 z = 0 at hz
  apply (tateCocycleClass_eq_zero_iff M 0 z hz).mpr
  have hf : d₀₁ M ((cochainsIso₀ M).hom z) = 0 := by
    have hd := congrArg (fun f => f.hom z) (comp_d₀₁_eq M)
    change d₀₁ M ((cochainsIso₀ M).hom z) =
      (cochainsIso₁ M).hom ((tateComplex M).d 0 1 z) at hd
    simpa only [hz, map_zero] using hd
  obtain ⟨b, hb⟩ := h _ hf
  refine ⟨(chainsIso₀ M).inv b, ?_⟩
  change (cochainsIso₀ M).inv (M.norm.hom
    ((chainsIso₀ M).hom ((chainsIso₀ M).inv b))) = z
  rw [Iso.inv_hom_id_apply, hb, Iso.hom_inv_id_apply]

/-- Tate degree minus one vanishing makes every norm-zero element an augmentation boundary. -/
theorem augmentation_exact_of_tate_neg_one (h : Limits.IsZero (tateCohomology M (-1)))
    (x : M) (hx : M.norm.hom x = 0) : ∃ b : G →₀ M, d₁₀ M b = x := by
  let z : (tateComplex M).X (-1) := (chainsIso₀ M).inv x
  have hz : (tateComplex M).d (-1) (-1 + 1) z = 0 := by
    change (cochainsIso₀ M).inv (M.norm.hom ((chainsIso₀ M).hom ((chainsIso₀ M).inv x))) = 0
    rw [Iso.inv_hom_id_apply, hx, map_zero]
  have := ModuleCat.isZero_iff_subsingleton.mp h
  obtain ⟨b, hb⟩ := (tateCocycleClass_eq_zero_iff M (-1) z hz).mp (Subsingleton.elim _ _)
  change (inhomogeneousChains M).d 1 0 b = z at hb
  refine ⟨(chainsIso₁ M).hom b, ?_⟩
  have hd := congrArg (fun f => f.hom b) (comp_d₁₀_eq M)
  change d₁₀ M ((chainsIso₁ M).hom b) =
    (chainsIso₀ M).hom ((inhomogeneousChains M).d 1 0 b) at hd
  rw [hb] at hd
  simpa only [z, Iso.inv_hom_id_apply] using hd

/-- Augmentation exactness on norm-zero elements kills Tate degree minus one. -/
theorem tate_neg_one_isZero_of_augmentation_exact
    (h : ∀ x : M, M.norm.hom x = 0 → ∃ b : G →₀ M, d₁₀ M b = x) :
    Limits.IsZero (tateCohomology M (-1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices hz : ∀ a : tateCohomology M (-1), a = 0 from ⟨fun a b => (hz a).trans (hz b).symm⟩
  intro a
  obtain ⟨z, hz, rfl⟩ := tateCocycleClass_surjective M (-1) a
  apply (tateCocycleClass_eq_zero_iff M (-1) z hz).mpr
  have hf : M.norm.hom ((chainsIso₀ M).hom z) = 0 := by
    have hd := congrArg (cochainsIso₀ M).hom hz
    change (cochainsIso₀ M).hom ((cochainsIso₀ M).inv
      (M.norm.hom ((chainsIso₀ M).hom z))) = (cochainsIso₀ M).hom 0 at hd
    simpa only [Iso.inv_hom_id_apply, map_zero] using hd
  obtain ⟨b, hb⟩ := h _ hf
  refine ⟨(chainsIso₁ M).inv b, ?_⟩
  have hd := congrArg (fun f => f.hom b) (eq_d₁₀_comp_inv M)
  change (tateComplex M).d (-2) (-1) ((chainsIso₁ M).inv b) =
    (chainsIso₀ M).inv (d₁₀ M b) at hd
  rw [hb, Iso.hom_inv_id_apply] at hd
  exact hd

end LocalClassFieldTheory

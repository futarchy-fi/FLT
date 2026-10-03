/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedNormExact
public import FLT.LocalClassFieldTheory.CoinducedShapiro
public import FLT.LocalClassFieldTheory.TateClassArithmetic

/-!
# Tate acyclicity of the concrete coinduced coefficient module

Shapiro vanishing and explicit exactness at the norm splice prove vanishing in
every integer degree of the actual Tate complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

local notation "C" => coinducedCoefficients M

/-- The coinduced Tate group in degree zero vanishes by norm surjectivity. -/
theorem coinducedTate_zero_isZero : Limits.IsZero (tateCohomology C 0) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices h : ∀ a : tateCohomology C 0, a = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  intro a
  obtain ⟨z, hz, rfl⟩ := tateCocycleClass_surjective C 0 a
  apply (tateCocycleClass_eq_zero_iff C 0 z hz).mpr
  change (tateComplex C).d 0 1 z = 0 at hz
  have hf : d₀₁ C ((cochainsIso₀ C).hom z) = 0 := by
    have h := congrArg (fun f => f.hom z) (comp_d₀₁_eq C)
    change d₀₁ C ((cochainsIso₀ C).hom z) =
      (cochainsIso₁ C).hom ((tateComplex C).d 0 1 z) at h
    simpa only [hz, map_zero] using h
  obtain ⟨b, hb⟩ := coinducedNorm_surjective_on_invariants M _ hf
  refine ⟨(chainsIso₀ C).inv b, ?_⟩
  change (cochainsIso₀ C).inv ((coinducedCoefficients M).norm.hom
    ((chainsIso₀ C).hom ((chainsIso₀ C).inv b))) = z
  rw [(chainsIso₀ C).inv_hom_id_apply, hb, (cochainsIso₀ C).hom_inv_id_apply]

/-- The coinduced Tate group in degree minus one vanishes by augmentation exactness. -/
theorem coinducedTate_neg_one_isZero : Limits.IsZero (tateCohomology C (-1)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices h : ∀ a : tateCohomology C (-1), a = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  intro a
  obtain ⟨z, hz, rfl⟩ := tateCocycleClass_surjective C (-1) a
  apply (tateCocycleClass_eq_zero_iff C (-1) z hz).mpr
  have hf : (coinducedCoefficients M).norm.hom ((chainsIso₀ C).hom z) = 0 := by
    have h := congrArg (cochainsIso₀ C).hom hz
    change (cochainsIso₀ C).hom ((cochainsIso₀ C).inv
      ((coinducedCoefficients M).norm.hom ((chainsIso₀ C).hom z))) = (cochainsIso₀ C).hom 0 at h
    simpa only [Iso.inv_hom_id_apply, map_zero] using h
  obtain ⟨b, hb⟩ := coinducedNorm_kernel M _ hf
  refine ⟨(chainsIso₁ C).inv b, ?_⟩
  have h := congrArg (fun f => f.hom b) (eq_d₁₀_comp_inv C)
  change (tateComplex C).d (-2) (-1) ((chainsIso₁ C).inv b) =
    (chainsIso₀ C).inv (d₁₀ C b) at h
  rw [hb, Iso.hom_inv_id_apply] at h
  convert h using 1
  rfl

/-- Every integer Tate group of the concrete coinduced module vanishes. -/
theorem coinducedTate_isZero (n : ℤ) : Limits.IsZero (tateCohomology C n) := by
  rcases n with n | n
  · cases n with
    | zero => exact coinducedTate_zero_isZero M
    | succ n =>
      exact (coinducedCoefficients_cohomology_isZero M n).of_iso
        ((TateCohomology.isoGroupCohomology (n + 1)).app C)
  · cases n with
    | zero => exact coinducedTate_neg_one_isZero M
    | succ n =>
      exact (coinducedCoefficients_homology_isZero M n).of_iso
        ((TateCohomology.isoGroupHomology _ (n + 1) (by omega)).app C)

end LocalClassFieldTheory

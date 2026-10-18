/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerExtensionCharts

/-!
# Finite-order equations from support on a Noetherian scheme

A support containment gives one global power inclusion, using a finite affine
cover. Applied to a schematic image, it constructs an actual factorization
through an ideal-power neighborhood without reducing the source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IdealSheafSupportPower
open Scheme.IdealSheafData
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{0}} [IsNoetherian X]

/-- A radical containment has a uniform exponent on the original Noetherian scheme. -/
theorem exists_pow_le (I J : X.IdealSheafData) (h : I ≤ J.radical) :
    ∃ n : ℕ, I ^ (n + 1) ≤ J := by
  classical
  obtain ⟨ι, hι, V, hV⟩ := IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)
  let _ := Fintype.ofFinite ι
  have hn (i : ι) : ∃ n : ℕ, I.ideal (V i) ^ n ≤ J.ideal (V i) := by
    let _ := IsLocallyNoetherian.component_noetherian (V i)
    exact Ideal.exists_pow_le_of_le_radical_of_fg (h (V i)) (IsNoetherian.noetherian _)
  choose n hn using hn
  refine ⟨Finset.univ.sup n, le_of_iSup_eq_top V hV fun i ↦ ?_⟩
  change I.ideal (V i) ^ (Finset.univ.sup n + 1) ≤ J.ideal (V i)
  exact (Ideal.pow_le_pow_right
    ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))).trans (hn i)

/-- Closed support containment yields equations in the unchanged ideal sheaves. -/
theorem exists_pow_le_of_support (I J : X.IdealSheafData)
    (h : J.support ≤ I.support) : ∃ n : ℕ, I ^ (n + 1) ≤ J := by
  apply exists_pow_le
  rw [← vanishingIdeal_support]
  exact le_support_iff_le_vanishingIdeal.mp h

/-- A compact scheme supported on a closed locus factors through a finite thickening. -/
theorem exists_factor (I : X.IdealSheafData) (f : Y ⟶ X) [QuasiCompact f]
    (h : Set.range f ⊆ I.support) :
    ∃ (n : ℕ) (g : Y ⟶ (I ^ (n + 1)).subscheme),
      g ≫ (I ^ (n + 1)).subschemeι = f := by
  have hs : f.ker.support ≤ I.support := by
    rw [← SetLike.coe_subset_coe, f.support_ker]
    exact I.support.isClosed.closure_subset_iff.mpr h
  obtain ⟨n, hn⟩ := exists_pow_le_of_support I f.ker hs
  refine ⟨n, f.toImage ≫ inclusion hn, ?_⟩
  rw [Category.assoc, inclusion_subschemeι, f.toImage_imageι]

end FLT.Mazur.IdealSheafSupportPower

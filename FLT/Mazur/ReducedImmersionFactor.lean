/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Factoring reduced tests through an immersion

A reduced scheme test factors through an immersion precisely when its whole
image lies in that immersion. This applies in particular to residue-field tests.
The reduced hypothesis is essential and is not imposed on the immersed scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ReducedImmersionFactor
variable {X Y T : Scheme.{0}} [IsReduced T]

/-- Reduced tests kill the full kernel ideal whenever their image lies in the given image. -/
theorem kernel_le_of_range (i : X ⟶ Y) (t : T ⟶ Y)
    (h : Set.range t ⊆ Set.range i) : i.ker ≤ t.ker := by
  have hz : (i.ker.comap t).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap]
    apply top_le_iff.mp
    intro x _
    exact i.range_subset_ker_support (h ⟨x, rfl⟩)
  have he : i.ker.comap t = ⊥ :=
    Scheme.IdealSheafData.support_eq_top_iff.mp hz
  rw [← Scheme.IdealSheafData.map_bot t]
  exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr he.le

/-- Image containment constructs the actual unique scheme factor through any immersion. -/
theorem existsUnique_factor (i : X ⟶ Y) [IsImmersion i] (t : T ⟶ Y)
    (h : Set.range t ⊆ Set.range i) : ∃! u : T ⟶ X, u ≫ i = t := by
  let v := IsOpenImmersion.lift i.coborderRange.ι t
    (h.trans (by
      rw [Scheme.Opens.range_ι]
      exact subset_coborder))
  have hv : v ≫ i.coborderRange.ι = t := IsOpenImmersion.lift_fac _ _ _
  have hi : Set.range v ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    refine ⟨y, i.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    change (i.liftCoborder ≫ i.coborderRange.ι) y =
      (v ≫ i.coborderRange.ι) x
    rw [Scheme.Hom.liftCoborder_ι, hv, hy]
  let u := IsClosedImmersion.lift i.liftCoborder v (kernel_le_of_range _ _ hi)
  have hu : u ≫ i = t := by
    rw [← Scheme.Hom.liftCoborder_ι i, ← Category.assoc,
      IsClosedImmersion.lift_fac, hv]
  exact ⟨u, hu, fun z hz ↦ (cancel_mono i).mp (hz.trans hu.symm)⟩

end FLT.Mazur.ReducedImmersionFactor

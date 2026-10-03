/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicTateVanishing
public import FLT.LocalClassFieldTheory.NormalNormAugmentation

/-!
# The reverse cyclic norm-splice criterion

For a cyclic group, augmentation is the image of a generator minus one.
Thus degree minus one vanishing also implies degree one vanishing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory Rep.FiniteCyclicGroup

/-- Cyclic degree minus one vanishing gives degree one vanishing. -/
theorem cyclic_tate_one_isZero_of_neg_one {k G : Type} [CommRing k] [Group G] [Fintype G]
    [IsCyclic G] (M : Rep k G) (h : Limits.IsZero (tateCohomology M (-1))) :
    Limits.IsZero (tateCohomology M 1) := by
  let := IsCyclic.commGroup (α := G)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have he : (subCompNormHom M g).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hm := norm_kernel_mem_augmentation M h x hx
    rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ g hg] at hm
    exact hm
  exact ((ShortComplex.exact_iff_isZero_homology _).mp he).of_iso
    (((TateCohomology.isoGroupCohomology 1).app M) ≪≫
      groupCohomologyIsoOdd M g hg 1 (by decide))

end LocalClassFieldTheory

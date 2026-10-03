/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CocycleDimensionShift
public import FLT.LocalClassFieldTheory.SubgroupTransferNorm

/-!
# Summing a two-cocycle in its first argument

These invariant sums compute the negative-degree two-extension operation.
Their subgroup transfer identity follows directly from the cocycle equation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (M : Rep k G) (c : cocycles₂ M)

/-- Sum a two-cocycle in its first group argument. -/
def twoCocycleSum (g : G) : M := ∑ h : G, c (h, g)

/-- The sum is fixed by the full group action. -/
theorem twoCocycleSum_fixed (g t : G) : M.ρ t (twoCocycleSum M c g) =
    twoCocycleSum M c g := by
  classical
  have hc (h : G) : M.ρ t (c (h, g)) = c (t * h, g) - c (t, h * g) + c (t, h) := by
    have he := (mem_cocycles₂_iff c).mp c.property t h g
    change c (t * h, g) + c (t, h) = M.ρ t (c (h, g)) + c (t, h * g) at he
    exact (eq_sub_of_add_eq he.symm).trans (by abel)
  simp only [twoCocycleSum, map_sum, hc, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hl : (∑ h : G, c (t * h, g)) = ∑ h : G, c (h, g) :=
    Equiv.sum_comp (Equiv.mulLeft t) (fun h => c (h, g))
  have hr : (∑ h : G, c (t, h * g)) = ∑ h : G, c (t, h) :=
    Equiv.sum_comp (Equiv.mulRight g) (fun h => c (t, h))
  rw [hl, hr, sub_add_cancel]

/-- The cocycle sum, viewed in invariant coefficients. -/
def twoCocycleSumInvariant (g : G) : M.ρ.invariants :=
  ⟨twoCocycleSum M c g, twoCocycleSum_fixed M c g⟩

/-- The coinduced norm of the primitive is the orbit embedding of its cocycle sum. -/
theorem twoCocyclePrimitive_norm (g : G) :
    (coinducedCoefficients M).norm.hom (twoCocyclePrimitive M c g) =
      (coinducedInclusion M).hom (twoCocycleSum M c g) := by
  classical
  funext t
  change (∑ h : G, (coinducedCoefficients M).ρ h) (twoCocyclePrimitive M c g) t = _
  simp only [LinearMap.sum_apply]
  change (∑ h : G, fun t : G => c (t * h, g)) t = M.ρ t (twoCocycleSum M c g)
  rw [Finset.sum_apply]
  rw [twoCocycleSum_fixed]
  exact Equiv.sum_comp (Equiv.mulLeft t) (fun h => c (h, g))

variable (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]

/-- Coset transfer of the restricted sum is the ambient cocycle sum. -/
theorem twoCocycleSum_transfer (g : H) :
    transferZero M H (∑ h : H, c (h, g)) = twoCocycleSum M c g := by
  classical
  have hc (q : G ⧸ H) (h : H) :
      M.ρ q.out (c (h, g)) = c (q.out * h, g) - c (q.out, (h * g : H)) + c (q.out, h) := by
    have he := (mem_cocycles₂_iff c).mp c.property q.out h g
    change c (q.out * h, g) + c (q.out, h) =
      M.ρ q.out (c (h, g)) + c (q.out, (h * g : H)) at he
    exact (eq_sub_of_add_eq he.symm).trans (by abel)
  rw [transferZero_apply]
  simp only [map_sum, hc, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hr (q : G ⧸ H) : (∑ h : H, c (q.out, (h * g : H))) = ∑ h : H, c (q.out, h) :=
    Equiv.sum_comp (Equiv.mulRight g) (fun h : H => c (q.out, h))
  simp only [hr, sub_add_cancel]
  exact (Fintype.sum_prod_type (fun qh : (G ⧸ H) × H => c (qh.1.out * qh.2, g))).symm.trans
    ((normCosetEquiv H).sum_comp (fun h => c (h, g)))

end LocalClassFieldTheory

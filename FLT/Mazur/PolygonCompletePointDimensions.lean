/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointAcyclic

/-!
# Exact point-power dimensions on every original field square

Universal vanishing eliminates the remaining H1 term in the proved Euler
formula. In particular the original pole-one, pole-two, pole-three and
pole-six spaces have dimensions one, two, three and six.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Each positive power of the actual retained point has H0 dimension equal to its exponent. -/
theorem completeCartesianPointPower_h0 (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Module.finrank L (ModuleScalarH q
      (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 0) = m := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let _ : Subsingleton (ModuleScalarH q
      (tensorPower (completeCartesianPointLine K n h s p q hs i) (a + 1)) 1) :=
    completeCartesianPointPower_affine_positive K n h s p q hs i a 0
  rw [completeCartesianPointLine_power_h0_eq, Module.finrank_zero_of_subsingleton, add_zero]

include hs in
/-- The same exact dimension holds for the pullback of the original complete coefficient. -/
theorem completePointPower_field_h0 (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Module.finrank L (ModuleScalarH q
      ((Scheme.Modules.pullback p).obj (tensorPower (completePointLine K n h i) m)) 0) = m :=
  ((moduleScalarHFunctor q 0).mapIso
    (completeCartesianPointPowerIso K n h s p q hs i m)).toLinearEquiv.finrank_eq.trans
      (completeCartesianPointPower_h0 K n h L s p q hs i m hm)

/-- The low-pole dimensions needed for pointed cubic coordinates hold on the original square. -/
theorem completeCartesianPointPower_low_h0 (i : Fin n) :
    (∀ m ∈ ({1, 2, 3, 6} : Finset ℕ), Module.finrank L (ModuleScalarH q
      (tensorPower (completeCartesianPointLine K n h s p q hs i) m) 0) = m) := by
  intro m hm
  apply completeCartesianPointPower_h0 K n h L s p q hs i m
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

end FLT.Mazur.PolygonInfinitesimalStages

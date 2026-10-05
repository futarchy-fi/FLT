/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurvePositiveDegreeAffineSection
public import FLT.Mazur.IdealTwistCohomologyVanishing
public import FLT.Mazur.TensorPowerReassociation

/-!
# Positive degree gives vanishing for every ideal coefficient

The affine section of a positive line power supplies a vanishing twist for
each ideal sheaf. Tensor-power reassociation returns the result to the original
line sheaf, with a strictly positive exponent. Turning this criterion into
an affine-section-open cover, and hence ampleness, is a separate obligation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback LineSectionTwistSystem

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hd : topologicalKrullDim X ≤ 1)

include hd in
/-- Every ideal coefficient admits a positive line-power twist with zero positive cohomology. -/
theorem exists_positive_ideal_power_cohomology_vanishing {L : X.Modules}
    (hL : LocallyFreeRankOne L) (hdeg : 0 < curveSheafDegree f L)
    (I : X.IdealSheafData) (q : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Subsingleton (ModuleH (tensor (idealModule I) (tensorPower L m)) (q + 1)) := by
  obtain ⟨d, hdpos, s, hs, hAffine⟩ := exists_nonzero_line_power_affine_section f hd hL hdeg
  obtain ⟨N, hN⟩ := idealCohomology_eventually_subsingleton f hd I (hL.tensorPower d)
    s hs hAffine q
  have hzero := hN (N + 1) (Nat.le_add_right N 1)
  let e : tensor (idealModule I) (tensorPower (tensorPower L d) (N + 1)) ≅
      tensor (idealModule I) (tensorPower L (d * (N + 1))) :=
    ModuleSheafTensor.congr (Iso.refl _) (tensorPowerMulIso L d (N + 1))
  have : Subsingleton ((moduleScalarHFunctor f (q + 1)).obj
      (tensor (idealModule I) (tensorPower (tensorPower L d) (N + 1)))) := hzero
  refine ⟨d * (N + 1), Nat.mul_pos hdpos (Nat.succ_pos N), ?_⟩
  exact (((moduleScalarHFunctor f (q + 1)).mapIso e).toLinearEquiv.symm).injective.subsingleton

end FLT.Mazur.FCurve

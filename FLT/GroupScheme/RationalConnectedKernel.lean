/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityClosedComponent
public import FLT.GroupScheme.RationalConnectedLevelTower
public import FLT.GroupScheme.SurjectiveSquareKernel
public import FLT.GroupScheme.AugmentationQuotientSquare

/-! # The original kernel equations on the connected level tower -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
variable {X Y : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)}

/-- The coordinate projection has precisely the original selected component ideal as kernel. -/
theorem FF.rationalIdentityComponentInclusion_ker (X : FF
    ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) :
    RingHom.ker X.rationalIdentityComponentInclusion.toAlgHom.toRingHom =
      X.rationalIdentityComponentIdeal := Ideal.mk_ker

/-- The kernel of a restricted closed immersion is the image of its original kernel. -/
theorem ModelHom.rationalIdentityMap_ker (f : ModelHom X Y)
    (hf : Function.Surjective f) :
    (RingHom.ker f.toAlgHom.toRingHom).map
        Y.rationalIdentityComponentInclusion.toAlgHom.toRingHom =
      RingHom.ker f.rationalIdentityMap.toAlgHom.toRingHom := by
  apply RingHom.map_ker_of_surjective_square f.toAlgHom.toRingHom
    Y.rationalIdentityComponentInclusion.toAlgHom.toRingHom
    X.rationalIdentityComponentInclusion.toAlgHom.toRingHom _ hf
    Y.rationalIdentityComponentInclusion_surjective
  · ext a
    rfl
  · rw [X.rationalIdentityComponentInclusion_ker, Y.rationalIdentityComponentInclusion_ker]
    exact f.rationalIdentityIdeal_map_of_surjective hf

/-- The actual augmentation ideal descends along the identity-component projections. -/
theorem ModelHom.rationalIdentityMap_augmentation (f : ModelHom X Y) :
    (HopfAlgebra.augmentationIdeal f).map
        X.rationalIdentityComponentInclusion.toAlgHom.toRingHom =
      HopfAlgebra.augmentationIdeal f.rationalIdentityMap :=
  HopfAlgebra.augmentationIdeal_map_of_quotient_square f
    X.rationalIdentityComponentInclusion Y.rationalIdentityComponentInclusion
    f.rationalIdentityMap Y.rationalIdentityComponentInclusion_surjective
    f.rationalIdentityMap_naturality.symm

/-- The restricted transitions satisfy the actual integral scheme-kernel equations. -/
theorem PDivisibleSystem.rationalConnected_kernel {height : ℕ}
    (X : PDivisibleSystem ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ) p height) (m n : ℕ) :
    HopfAlgebra.augmentationIdeal (X.rationalConnectedReduction (Nat.le_add_left n m)) =
      RingHom.ker (X.rationalConnectedInclusion (Nat.le_add_right m n)).toAlgHom.toRingHom := by
  rw [rationalConnectedReduction, rationalConnectedInclusion,
    ← ModelHom.rationalIdentityMap_augmentation, X.kernel,
    ModelHom.rationalIdentityMap_ker _ (X.closed _)]
end ThreeAdicPlan

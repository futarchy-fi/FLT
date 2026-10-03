/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIntegralQuotient
public import FLT.GroupScheme.HopfTorsor

/-!
# Equations of prescribed integral kernels

The quotient comparison preserves the augmentation and is surjective.
Consequently the original quotient and its contraction have the same kernel ideal.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- The prescribed quotient has the same augmentation equations as its contracted quotient. -/
theorem ModelHom.augmentationIdeal_eq_contracted {X Y : FF O K}
    (hp : 2 < p) (hY : KilledByPowerOf p Y) (f : ModelHom X Y)
    (hf : Function.Surjective (genericHom f)) :
    HopfAlgebra.augmentationIdeal f = (genericHom f).quotientKernelIdeal := by
  let c := f.quotientComparison hf
  have hc : Function.Surjective c := (f.quotientComparison_bijective p hp hY hf).2
  have he : RingHom.ker (Bialgebra.counitAlgHom O Y.CoordinateRing).toRingHom =
      (RingHom.ker (Bialgebra.counitAlgHom O
        (genericHom f).quotientCoordinates).toRingHom).comap c.toAlgHom.toRingHom := by
    ext y
    change Coalgebra.counit (R := O) y = 0 ↔ Coalgebra.counit (R := O) (c y) = 0
    rw [CoalgHomClass.counit_comp_apply]
  have hcomp := f.quotientComparisonComp hf
  unfold HopfAlgebra.augmentationIdeal
  conv_lhs => rw [← hcomp]
  change (RingHom.ker (Bialgebra.counitAlgHom O Y.CoordinateRing).toRingHom).map
      (((genericHom f).toFlatQuotient hf).toAlgHom.toRingHom.comp c.toAlgHom.toRingHom) = _
  rw [← Ideal.map_map, he, Ideal.map_comap_of_surjective c.toAlgHom.toRingHom hc]
  rfl

/-- Exact prescribed point maps identify the actual integral kernel equations. -/
theorem ModelHom.augmentationIdeal_eq_closure {S X Y : FF O K}
    (hp : 2 < p) (hY : KilledByPowerOf p Y)
    (i : GenericGaloisHom S X) (f : ModelHom X Y)
    (hf : Function.Surjective (genericHom f))
    (hexact : ∀ x, genericHom f x = 0 ↔ ∃ s, i s = x) :
    HopfAlgebra.augmentationIdeal f = i.closureIdeal := by
  rw [f.augmentationIdeal_eq_contracted p hp hY hf]
  exact i.quotientKernelIdealEqClosureIdeal (genericHom f) hf hexact

end ThreeAdicPlan

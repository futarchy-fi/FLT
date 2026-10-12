/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomMultiplicationLocus
public import FLT.Mazur.FiniteFlatIdealVanishingUniversal

/-!
# Universal tests for the global cyclic multiplication locus

The actual global locus represents killing the universal multiplication ideal
on the entire cartesian divisor product. No etaleness or reducedness condition
is imposed on the test scheme. Identifying this cartesian family with the
cyclic source reconstructed from each test parameter is a separate comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

instance cyclicHomUniversalMultiplicationLocusInclusion_closed :
    IsClosedImmersion (cyclicHomUniversalMultiplicationLocusInclusion n) :=
  cyclicHomMultiplicationLocusInclusion_closed n (𝟙 _)

/-- Global parameter tests factor exactly when they kill the actual universal pulled ideal. -/
theorem cyclicHomUniversalLocus_factorization_iff {T : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    (∃ k : T ⟶ cyclicHomUniversalMultiplicationLocus n,
      k ≫ cyclicHomUniversalMultiplicationLocusInclusion n = f) ↔
        (cyclicHomMultiplicationIdeal n (𝟙 _)).comap
          (pullback.snd f (cyclicHomDivisorProduct n (𝟙 _)).hom) = ⊥ :=
  FiniteFlatIdealVanishing.locus_factorization_iff
    (IsPullback.of_hasPullback f (cyclicHomDivisorProduct n (𝟙 _)).hom).flip _

/-- The universal locus kills the full universal multiplication ideal after actual base change. -/
theorem cyclicHomUniversalLocus_ideal_eq_bot :
    (cyclicHomMultiplicationIdeal n (𝟙 _)).comap
      (pullback.snd (cyclicHomUniversalMultiplicationLocusInclusion n)
        (cyclicHomDivisorProduct n (𝟙 _)).hom) = ⊥ :=
  FiniteFlatIdealVanishing.universalIdeal_eq_bot _

/-- A lift to the actual global locus is unique over the original auxiliary scheme. -/
theorem cyclicHomUniversalLocus_lift_unique {T : Scheme}
    (k l : T ⟶ cyclicHomUniversalMultiplicationLocus n)
    (h : k ≫ cyclicHomUniversalMultiplicationLocusInclusion n =
      l ≫ cyclicHomUniversalMultiplicationLocusInclusion n) : k = l :=
  (cancel_mono (cyclicHomUniversalMultiplicationLocusInclusion n)).mp h

end FLT.Mazur.UniversalWeierstrass

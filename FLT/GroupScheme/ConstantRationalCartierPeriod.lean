/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantRationalTateVectors
public import FLT.GroupScheme.RationalCartierFirstOrder
public import FLT.GroupScheme.RationalPlaceTateReducedUnramified
public import FLT.GroupScheme.PDivisibleRationalCartierPeriods
public import FLT.PadicHodgeTheory.ComplexCyclotomicFirstOrder
public import FLT.PadicHodgeTheory.ComplexCyclotomicLogOrder

/-! # The constant etale rational-place system has a nonzero cyclotomic period -/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ConstantRationalPower
open PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime] (hp : 2 < p)

/-- The actual root pairing is the repository's chosen complex cyclotomic sequence. -/
theorem cartierRoot_generator (n : ℕ) :
    rationalCartierRoot (system p hp) (cyclotomicVector p hp) (generator p hp) n =
      (complexCyclotomicSequence p).val n := by
  apply Subtype.ext
  change rationalPlaceComplexMap p
    ((system p hp).cartierTatePairing (cyclotomicVector p hp) (generator p hp) n : _) = _
  rw [tatePairing_generator]
  exact rationalCyclotomicRoot_map p n

/-- Equality holds for the whole original root sequence. -/
theorem cartierRootSequence_generator :
    rationalCartierRootSequence (system p hp) (cyclotomicVector p hp) (generator p hp) =
      complexCyclotomicSequence p := by
  apply Subtype.ext
  funext n
  exact cartierRoot_generator p hp n

/-- The original Cartier tilt element is exactly epsilon. -/
theorem cartierTilt_generator :
    rationalCartierTilt (system p hp) (cyclotomicVector p hp) (generator p hp) =
      complexCyclotomicTilt p := by
  unfold rationalCartierTilt
  rw [cartierRootSequence_generator]
  rfl

/-- The original logarithmic Cartier period is exactly t, not zero. -/
theorem cartierPeriod_generator :
    rationalCartierPeriod (system p hp) (cyclotomicVector p hp) (generator p hp) =
      complexCyclotomicLog p := by
  unfold rationalCartierPeriod
  simp only [cartierTilt_generator]
  rfl

/-- The first-order period is the actual integral cyclotomic difference at each precision. -/
theorem cartierFirstOrder_generator (s : ℕ) :
    (rationalCartierFirstOrder (system p hp) s (cyclotomicVector p hp) (generator p hp) :
      ComplexIntegralThickening p 2 s) = complexCyclotomicFirstOrder p s := by
  change Ideal.Quotient.mk _ (WittVector.teichmuller p (rationalCartierTilt _ _ _) - 1) = _
  rw [cartierTilt_generator]
  rfl

/-- The constructed tangent pairing of this same etale system is zero at every precision. -/
theorem reducedCartier_generator (s : ℕ) :
    rationalPlaceTateReducedCartier (system p hp) s (cyclotomicVector p hp) (generator p hp) =
      0 := by
  let : Algebra.Etale
      ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      ((system p hp).level s).CoordinateRing := levelEtale p s
  exact rationalPlaceTateReducedCartier_unramified _ _ _ _

/-- The specialized W57 equality itself fails at a positive precision on an actual system. -/
theorem firstOrder_comparison_fails : ∃ s : ℕ, 0 < s ∧
    rationalPlaceTateReducedCartier (system p hp) s (cyclotomicVector p hp) (generator p hp) ≠
      rationalCartierFirstOrder (system p hp) s (cyclotomicVector p hp) (generator p hp) := by
  obtain ⟨s, hs, hn⟩ := complexCyclotomicFirstOrder_exists_pos p
  refine ⟨s, hs, ?_⟩
  rw [reducedCartier_generator]
  intro he
  apply hn
  exact (cartierFirstOrder_generator p hp s).symm.trans (congrArg Subtype.val he.symm)

/-- The logarithmic pairing is nonzero, despite vanishing of the entire reduced tangent pairing. -/
theorem cartierPeriod_generator_ne_zero :
    rationalCartierPeriod (system p hp) (cyclotomicVector p hp) (generator p hp) ≠ 0 := by
  rw [cartierPeriod_generator]
  exact complexCyclotomicLog_ne_zero p

end ThreeAdicPlan.ConstantRationalPower

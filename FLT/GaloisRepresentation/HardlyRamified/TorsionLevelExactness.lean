/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TorsionModelTransitions
public import FLT.GroupScheme.RationalIntegralKernel

/-!
# Integral exactness of the actual hardly ramified torsion levels

The original domain supplies injective generic inclusions. Small ramification
makes these integral closed immersions and the reductions faithfully flat.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.IsHardlyRamified
open ThreeAdicPlan PrimePower

variable {p : ℕ} [Fact p.Prime] {hpodd : Odd p}
  {R V : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
  [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology ℤ_[p] R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  {hV : Module.rank R V = 2} {ρ : GaloisRep ℚ R V}
  (hρ : IsHardlyRamified hpodd hV ρ)

variable [IsDomain R]

/-- The original domain's p-power inclusion is injective on chosen generic points. -/
theorem torsionGenericInclusion_injective (m n : ℕ) :
    Function.Injective (hρ.torsionGenericInclusion m n) := by
  have hpR : (p : R) ≠ 0 := by
    intro h
    have h' : (p : ℤ_[p]) = 0 := FaithfulSMul.algebraMap_injective ℤ_[p] R
      (by simpa only [map_natCast, map_zero] using h)
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h'
  exact (hρ.torsionPoints (m + n)).symm.injective.comp
    ((tensorInclusion_injective (V := V) hpR m n).comp (hρ.torsionPoints m).injective)

/-- The actual integral level inclusion is a closed immersion. -/
theorem torsionInclusion_surjective (m n : ℕ) :
    Function.Surjective (hρ.torsionInclusion m n) := by
  apply ModelHom.closed_of_rational_power p (torsion_prime_gt_two (hpodd := hpodd))
    (hρ.torsionModel_killedByPower m)
  rw [genericHom_torsionInclusion]
  exact hρ.torsionGenericInclusion_injective m n

omit [IsDomain R] in
/-- The actual integral level reduction is faithfully flat. -/
theorem torsionReduction_faithfullyFlat (m n : ℕ) :
    (hρ.torsionReduction m n).toAlgHom.toRingHom.FaithfullyFlat := by
  apply ModelHom.faithfullyFlat_of_rational_power p
    (torsion_prime_gt_two (hpodd := hpodd)) (hρ.torsionModel_killedByPower n)
  rw [genericHom_torsionReduction]
  exact hρ.torsionGenericReduction_surjective m n

omit [IsDomain R] in
/-- The contracted quotient kernel has exactly the equations of the inclusion's closure. -/
theorem torsion_kernelIdeal_eq_closureIdeal (m n : ℕ) :
    (hρ.torsionGenericReduction m n).quotientKernelIdeal =
      (hρ.torsionGenericInclusion m n).closureIdeal :=
  GenericGaloisHom.quotientKernelIdealEqClosureIdeal _ _
    (hρ.torsionGenericReduction_surjective m n) (hρ.torsionGeneric_exact m n)

/-- The prescribed lower level is isomorphic to its closed generic image. -/
def torsionKernelClosureIso (m n : ℕ) :
    (hρ.torsionModel m).Iso
      ((genericHom (hρ.torsionInclusion m n)).closure
        (by rw [genericHom_torsionInclusion]; exact hρ.torsionGenericInclusion_injective m n)) :=
  ModelHom.closureIso _ _ (hρ.torsionInclusion_surjective m n)

omit [IsDomain R] in
/-- These are the kernel equations of the actual integral reduction. -/
theorem torsion_actual_kernelIdeal_eq (m n : ℕ) :
    HopfAlgebra.augmentationIdeal (hρ.torsionReduction m n) =
      (hρ.torsionGenericInclusion m n).closureIdeal := by
  apply ModelHom.augmentationIdeal_eq_closure p (torsion_prime_gt_two (hpodd := hpodd))
    (hρ.torsionModel_killedByPower n)
  · rw [genericHom_torsionReduction]
    exact hρ.torsionGenericReduction_surjective m n
  · intro x
    rw [hρ.genericHom_torsionReduction m n]
    exact hρ.torsionGeneric_exact m n x

/-- The scheme kernel of the actual reduction is the prescribed lower integral level. -/
def torsionKernelCoordinatesEquiv (m n : ℕ) :
    ((hρ.torsionModel (m + n)).CoordinateRing ⧸
      HopfAlgebra.augmentationIdeal (hρ.torsionReduction m n)) ≃ₐ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
          (hρ.torsionModel m).CoordinateRing := by
  rw [hρ.torsion_actual_kernelIdeal_eq]
  have e : ((hρ.torsionModel (m + n)).CoordinateRing ⧸
      (genericHom (hρ.torsionInclusion m n)).closureIdeal) ≃ₐ[
        (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ]
          (hρ.torsionModel m).CoordinateRing := (hρ.torsionKernelClosureIso m n).toAlgEquiv
  rw [hρ.genericHom_torsionInclusion m n] at e
  exact e

end GaloisRepresentation.IsHardlyRamified

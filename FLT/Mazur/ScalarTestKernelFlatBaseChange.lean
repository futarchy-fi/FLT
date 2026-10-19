/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarKernelExtension
public import FLT.Mazur.ScalarTestLocalizationKernels
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Full principal-test kernels commute with flat scalar base change

The actual tensor product principal chart has exactly the extended original
scalar kernel. No finite presentation or reducedness hypothesis is needed.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarTestLocalization
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S] (b : B)
local notation "B'" => S ⊗[R] B
local notation "j" => Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B)

/-- The full localization commutes with the scalar tensor product. -/
def flatTestChartEquiv :
    (S ⊗[R] Localization.Away b) ≃ₐ[S] Localization.Away (j b) := by
  let _ : IsLocalization ((Submonoid.powers b).map j) (Localization.Away (j b)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact IsLocalization.tensorProductEquivOfMapIncludeRight R S
    (Submonoid.powers b) (Localization.Away b) (Localization.Away (j b))

/-- Scalar kernels commute with flat extension as ideals, retaining every nilpotent equation. -/
theorem testKernel_flat_baseChange :
    testKernel (algebraMap S B') (j b) =
      (testKernel (algebraMap R B) b).map (algebraMap R S) := by
  have he : RingHom.ker (algebraMap S (Localization.Away (j b))) =
      RingHom.ker (algebraMap S (S ⊗[R] Localization.Away b)) := by
    ext x
    change algebraMap S (Localization.Away (j b)) x = 0 ↔ _
    rw [← (flatTestChartEquiv (R := R) S b).commutes x]
    exact (flatTestChartEquiv (R := R) S b).injective.eq_iff' (map_zero _)
  change RingHom.ker ((algebraMap B' (Localization.Away (j b))).comp
    (algebraMap S B')) = _
  rw [← IsScalarTower.algebraMap_eq S B', he,
    FlatScalarKernelExtension.scalar_kernel_eq]
  congr 1

/-- Any point of a flat scalar branch tests precisely the original contracted kernel. -/
theorem testKernel_flat_le_prime_iff (Q : PrimeSpectrum S) :
    testKernel (algebraMap S B') (j b) ≤ Q.asIdeal ↔
      testKernel (algebraMap R B) b ≤ Q.asIdeal.comap (algebraMap R S) := by
  rw [testKernel_flat_baseChange, Ideal.map_le_iff_le_comap]

end FLT.Mazur.ScalarTestLocalization

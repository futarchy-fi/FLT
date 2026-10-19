/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarTestKernelFlatBaseChange
public import FLT.Mazur.ScalarTestKernelProducts

/-!
# Arbitrary flat scalar base change of finite-test nilpotence opens

Exact kernel transport identifies the scalar open even when the flat scalar
algebra is not finitely presented. The indexed product also retains its full
ideal structure; repeated tests after base change are not silently removed.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarTestLocalization
open ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S] (a : Finset B)
local notation "B'" => S ⊗[R] B
local notation "j" => Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B)

/-- The finite indexed kernel product commutes with arbitrary flat scalar extension. -/
theorem kernelProduct_flat_indexed :
    (∏ b ∈ a, testKernel (algebraMap S B') (j b)) =
      (kernelProduct (algebraMap R B) a).map (algebraMap R S) := by
  classical
  simp only [testKernel_flat_baseChange, kernelProduct]
  induction a using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | @insert b a hb ih => simp only [Finset.prod_insert hb, Ideal.map_mul, ih]

/-- Full scalar-local nilpotence is unchanged at the contracted prime of any flat branch. -/
theorem scalarNilpotenceOpen_flat_iff (Q : PrimeSpectrum S) :
    Q ∈ scalarNilpotenceOpen (algebraMap S B')
        (Ideal.span (j '' (a : Set B))) ↔
      PrimeSpectrum.comap (algebraMap R S) Q ∈
        scalarNilpotenceOpen (algebraMap R B) (Ideal.span (a : Set B)) := by
  classical
  rw [← Finset.coe_image, mem_scalarNilpotenceOpen_iff_kernels,
    mem_scalarNilpotenceOpen_iff_kernels]
  constructor
  · intro h b hb
    exact (not_congr (testKernel_flat_le_prime_iff S b Q)).mp
      (h (j b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
  · intro h b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact (not_congr (testKernel_flat_le_prime_iff S c Q)).mpr (h c hc)

/-- Equality of full nilpotence opens needs flatness, with no finite-presentation assumption. -/
theorem scalarNilpotenceOpen_flat_preimage :
    (scalarNilpotenceOpen (algebraMap S B') (Ideal.span (j '' (a : Set B))) :
        Set (PrimeSpectrum S)) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        (scalarNilpotenceOpen (algebraMap R B) (Ideal.span (a : Set B)) :
          Set (PrimeSpectrum R)) := by
  ext Q
  exact scalarNilpotenceOpen_flat_iff S a Q

end FLT.Mazur.ScalarTestLocalization

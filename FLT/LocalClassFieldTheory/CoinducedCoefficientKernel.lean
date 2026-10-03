/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedSubgroupShift

/-!
# A coefficient kernel for reverse dimension shifting

For a finite group, the weighted sum of a coinduced function surjects onto the
original representation. Its actual kernel supplies the reverse shift.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory CategoryTheory.Limits

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- Weighted sum from right-translation functions to the original representation. -/
def coinducedAugmentation : coinducedCoefficients M ⟶ M := Rep.ofHom
  ⟨∑ g : G, (M.ρ g⁻¹).comp (LinearMap.proj g), fun h => by
    ext f
    change (∑ g : G, (M.ρ g⁻¹).comp (LinearMap.proj g))
      ((coinducedCoefficients M).ρ h f) =
        M.ρ h ((∑ g : G, (M.ρ g⁻¹).comp (LinearMap.proj g)) f)
    simp only [LinearMap.sum_apply, map_sum]
    apply Fintype.sum_equiv (Equiv.mulRight h)
    intro g
    change M.ρ g⁻¹ (f (g * h)) = M.ρ h (M.ρ (g * h)⁻¹ (f (g * h)))
    simp only [← Module.End.mul_apply, ← map_mul]
    simp⟩

/-- A point mass at the identity proves surjectivity of the weighted sum. -/
theorem coinducedAugmentation_surjective : Function.Surjective (coinducedAugmentation M).hom := by
  classical
  intro x
  refine ⟨Pi.single 1 x, ?_⟩
  change (∑ g : G, (M.ρ g⁻¹).comp (LinearMap.proj g)) (Pi.single 1 x) = x
  simp [LinearMap.sum_apply, Pi.single_apply, apply_ite]

/-- The concrete reverse-shift coefficient module is a kernel. -/
abbrev kernelCoefficients : Rep k G := kernel (coinducedAugmentation M)

/-- The kernel, coinduced functions, and weighted sum form a coefficient sequence. -/
def coinducedKernelSequence : ShortComplex (Rep k G) :=
  ShortComplex.mk (kernel.ι (coinducedAugmentation M)) (coinducedAugmentation M)
    (kernel.condition _)

/-- The coefficient kernel sequence is short exact. -/
theorem coinducedKernelSequence_shortExact : (coinducedKernelSequence M).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := inferInstanceAs (Mono (kernel.ι (coinducedAugmentation M)))
  epi_g := (Rep.epi_iff_surjective _).mpr (coinducedAugmentation_surjective M)

/-- Restricting the coefficient kernel sequence preserves short exactness. -/
theorem coinducedKernelSubgroupSequence_shortExact (H : Subgroup G) :
    ((coinducedKernelSequence M).map (Rep.resFunctor H.subtype)).ShortExact :=
  (Rep.shortExact_res H.subtype).mpr (coinducedKernelSequence_shortExact M)

/-- The reverse shift is an actual connecting isomorphism on every finite subgroup. -/
def coinducedKernelSubgroupShift (H : Subgroup G) [Fintype H] (n : ℤ) :
    tateCohomology (Rep.res H.subtype M) n ≅
      tateCohomology (Rep.res H.subtype (kernelCoefficients M)) (n + 1) := by
  have : IsIso (TateCohomology.δ (coinducedKernelSubgroupSequence_shortExact M H) n) :=
    ShortComplex.SnakeInput.isIso_δ _ (coinducedSubgroupTate_isZero M H n)
      (coinducedSubgroupTate_isZero M H (n + 1))
  exact asIso (TateCohomology.δ (coinducedKernelSubgroupSequence_shortExact M H) n)

/-- The unrestricted reverse shift is the boundary of the same kernel sequence. -/
def coinducedKernelShift (n : ℤ) :
    tateCohomology M n ≅ tateCohomology (kernelCoefficients M) (n + 1) := by
  have : IsIso (TateCohomology.δ (coinducedKernelSequence_shortExact M) n) :=
    ShortComplex.SnakeInput.isIso_δ _ (coinducedTate_isZero M n)
      (coinducedTate_isZero M (n + 1))
  exact asIso (TateCohomology.δ (coinducedKernelSequence_shortExact M) n)

end LocalClassFieldTheory

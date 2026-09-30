/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentComparisonLocus
public import FLT.Mazur.IdealPowerExtensionCharts

/-!
# Coherent decomposition over a union of closed sets

Stacks 01YD: a coherent sheaf supported on a union of two closed sets is an
extension of sheaves supported on the individual sets. The subobject is an
actual ideal-power multiple, and the quotient is its actual cokernel.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}} [IsNoetherian X]

/-- Support in an ideal's zero locus forces an actual ideal-power multiple to vanish. -/
theorem exists_isZero_power (I : X.IdealSheafData) (M : X.Modules)
    [M.IsFinitePresentation] (hM : support M ⊆ I.support) :
    ∃ n : ℕ, IsZero (power I n M) := by
  have hz : IsZero (M.restrict (complement I).ι) :=
    (isZero_restrict_iff M _).mpr (fun _ hx hm ↦ hx (hM hm))
  obtain ⟨n, hn⟩ := IdealPowerExtensionCharts.exists_global_equalizer I (𝟙 M) 0
    (hz.eq_of_src _ _)
  have hi : inclusion (I ^ n) M = 0 := by simpa using hn
  refine ⟨n, ?_⟩
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (inclusion (I ^ n) M)]
  simp [hi]

/-- Power-multiple quotients are supported in the original ideal's zero locus. -/
theorem support_cokernel_power_subset (I : X.IdealSheafData) (M : X.Modules)
    [M.IsFinitePresentation] (n : ℕ) :
    support (cokernel (inclusion (I ^ n) M)) ⊆ I.support := by
  let R := restrictFunctor (complement I).ι
  have := power_inclusion_complement I n M
  have hz : IsZero ((cokernel (inclusion (I ^ n) M)).restrict (complement I).ι) :=
    (PreservesCokernel.iso R (inclusion (I ^ n) M)).isZero_iff.mpr
      (isZero_cokernel_of_epi (R.map (inclusion (I ^ n) M)))
  intro x hx
  by_contra hn
  exact (isZero_restrict_iff _ _).mp hz x hn hx

/-- On a two-closed-set support bound, a power of the second ideal is supported
on the first set. The exponent is obtained on its open complement. -/
theorem exists_power_support_subset (M : X.Modules) [M.IsFinitePresentation]
    (Z₁ Z₂ : Closeds X) (hM : support M ⊆ (Z₁ : Set X) ∪ Z₂) :
    ∃ n : ℕ, support (power (Scheme.IdealSheafData.vanishingIdeal Z₂) n M) ⊆ Z₁ := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z₂
  let U : X.Opens := Z₁.compl
  have : IsNoetherian U.toScheme := by
    have : NoetherianSpace U.toScheme :=
      U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    exact ⟨⟩
  have := coherentPresentation_restrict U.ι M
  have hI : support (M.restrict U.ι) ⊆ (I.comap U.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    intro x hx
    have hm := hM ((mem_support_restrict M U.ι x).mp hx)
    have hx₂ : U.ι x ∈ Z₂ := hm.resolve_left x.property
    simpa [I] using hx₂
  obtain ⟨n, hn⟩ := exists_isZero_power (I.comap U.ι) (M.restrict U.ι) hI
  have hz : IsZero ((power I n M).restrict U.ι) :=
    (powerRestrictIso I n M U.ι).isZero_iff.mpr hn
  refine ⟨n, fun x hx ↦ ?_⟩
  by_contra hnot
  exact (isZero_restrict_iff _ U).mp hz x hnot hx

/-- Supported decomposition (Stacks 01YD), with constructed maps and coherent terms. -/
theorem exists_supported_decomposition (M : X.Modules) [M.IsFinitePresentation]
    (Z₁ Z₂ : Closeds X) (hM : support M ⊆ (Z₁ : Set X) ∪ Z₂) :
    ∃ (G₁ G₂ : X.Modules) (f : G₁ ⟶ M) (g : M ⟶ G₂) (w : f ≫ g = 0),
      CoherentSequence (ShortComplex.mk f g w) ∧
        support G₁ ⊆ Z₁ ∧ support G₂ ⊆ Z₂ := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z₂
  obtain ⟨n, hn⟩ := exists_power_support_subset M Z₁ Z₂ hM
  let f := inclusion (I ^ n) M
  refine ⟨power I n M, cokernel f, f, cokernel.π f, cokernel.condition f,
    coherent_cokernelSequence f, hn, ?_⟩
  simpa [I] using support_cokernel_power_subset I M n

end FLT.Mazur.FCurve.CoherentDevissage

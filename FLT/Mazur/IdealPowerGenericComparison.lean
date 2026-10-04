/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerExtensionGluing
public import FLT.Mazur.GenericIdealSupport

/-!
# Reversing a generic comparison after an ideal power

A coherent comparison invertible at a point has an inverse on an open
neighborhood. Extend that inverse from an ideal-power multiple of its target.
Both errors of the resulting map omit the point. This supplies the direction
of comparison needed by support induction without kernel H¹ vanishing.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
open FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility

universe u

namespace FLT.Mazur.IdealPowerGenericComparison

variable {X : Scheme.{u}} [IsNoetherian X]
  {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation]

/-- Reverse a comparison at a point by extending its local inverse from an actual ideal power. -/
theorem exists_reverse (a : M ⟶ N) (x : X) [IsIso ((stalk x).map a)] :
    ∃ (I : X.IdealSheafData) (n : ℕ), x ∈ complement I ∧
      ∃ b : power I n N ⟶ M, IsIso ((stalk x).map b) := by
  let U := comparisonOpen a
  let I := Scheme.IdealSheafData.vanishingIdeal U.compl
  have hU : complement I = U := by
    have hs : I.support = U.compl :=
      SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
    change I.support.compl = U
    rw [hs, TopologicalSpace.Opens.compl_compl]
  have hx : x ∈ complement I := by
    rw [hU]
    exact (mem_comparisonOpen_iff a x).mpr inferInstance
  have hi : IsIso ((restrictFunctor (complement I).ι).map a) :=
    isIso_restrict_of_le_comparisonOpen a _ (le_of_eq hU)
  obtain ⟨n, b, hb⟩ := IdealPowerExtensionGluing.exists_ideal_power_extension I N M
    (inv ((restrictFunctor (complement I).ι).map a))
  have := power_inclusion_complement I n N
  have : IsIso ((restrictFunctor (complement I).ι).map b) := by
    rw [hb]
    infer_instance
  exact ⟨I, n, hx, b, GenericIdealInjection.stalk_isIso_of_restrict b _ x hx⟩

/-- The reverse comparison has kernel and cokernel on strictly smaller supports. -/
theorem exists_reverse_supported (a : M ⟶ N) (x : X)
    [IsIso ((stalk x).map a)] (Z : Set X) (hx : x ∈ Z)
    (hM : support M ⊆ Z) (hN : support N ⊆ Z) :
    ∃ (I : X.IdealSheafData) (n : ℕ), x ∈ complement I ∧
      ∃ b : power I n N ⟶ M, IsIso ((stalk x).map b) ∧
        support (kernel b) ⊂ Z ∧ support (cokernel b) ⊂ Z := by
  obtain ⟨I, n, hI, b, hb⟩ := exists_reverse a x
  let := hb
  refine ⟨I, n, hI, b, hb, ?_, GenericIdealSupport.cokernel_support_ssubset b x Z hx hM⟩
  refine ⟨(support_subset_of_mono (kernel.ι b)).trans
    ((support_subset_of_mono (inclusion (I ^ n) N)).trans hN), ?_⟩
  intro h
  exact ((isIso_stalk_iff_notMem_support b x).mp hb).1 (h hx)

end FLT.Mazur.IdealPowerGenericComparison

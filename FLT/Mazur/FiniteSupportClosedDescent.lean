/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GlobalClosedModuleDescent
public import FLT.Mazur.CoherentSupportedDecomposition
public import FLT.Mazur.FiniteSchemeLineTwist

/-!
# Coherent finite-support sheaves descend to finite closed subschemes

An actual ideal power kills a coherent sheaf with finite support. Closed descent
then realizes the sheaf as a coherent pushforward from a finite scheme. No
closed-subscheme presentation is assumed as input.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open CoherentDevissage FLT.Mazur.GlobalIdealPower

variable {k : Type} [Field k] {X : Scheme}

/-- A zero ideal-action image means that the ideal kills every affine section. -/
theorem idealKilled_of_isZero_multiple [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
    (h : IsZero (multiple I M)) : IdealKilled I M := by
  intro U r hr m
  have hm : r • m ∈ LinearMap.range ((inclusion I M).val.app (op U.1)).hom := by
    rw [inclusion_range]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  obtain ⟨a, ha⟩ := hm
  have hz : inclusion I M = 0 := h.eq_of_src _ _
  rw [← ha]
  change (inclusion I M).app U.1 a = 0
  rw [hz]
  rfl

/-- A finite support bound supplies an actual annihilating ideal power. -/
theorem exists_idealPower_killed [IsNoetherian X]
    (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
    (hM : support M ⊆ I.support) : ∃ n : ℕ, IdealKilled (I ^ n) M := by
  obtain ⟨n, hn⟩ := exists_isZero_power I M hM
  exact ⟨n, idealKilled_of_isZero_multiple (I ^ n) M hn⟩

/-- A closed subscheme with finitely many points is finite over the field. -/
theorem finiteClosed_of_finite_support
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (I : X.IdealSheafData) (hI : (I.support : Set X).Finite) :
    IsFinite (I.subschemeι ≫ f) := by
  have : Finite I.subscheme := (Set.finite_range_iff I.subschemeι.isClosedEmbedding.injective).mp
    (I.range_subschemeι.symm ▸ hI)
  have : LocallyQuasiFinite (I.subschemeι ≫ f) :=
    locallyQuasiFinite_iff_finite_preimage_singleton.mpr (fun _ ↦ Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite (I.subschemeι ≫ f)

/-- A coherent finite-support sheaf is an actual coherent finite closed pushforward. -/
theorem exists_finiteClosed_descent (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : X.Modules) [M.IsFinitePresentation] (hM : (support M).Finite) :
    ∃ (I : X.IdealSheafData) (N : I.subscheme.Modules),
      IsFinite (I.subschemeι ≫ f) ∧ N.IsFinitePresentation ∧
        Nonempty ((pushforward I.subschemeι).obj N ≅ M) := by
  have := Chow.source_isNoetherian f
  let I := Scheme.IdealSheafData.vanishingIdeal (closedSupport M)
  have hI : (I.support : Set X) = support M := by simp [I, closedSupport]
  obtain ⟨n, hn⟩ := exists_idealPower_killed I M (by rw [hI])
  have hp : ((I ^ n).support : Set X) ⊆ I.support := by
    cases n <;> simp
  have hf := finiteClosed_of_finite_support f (I ^ n) ((hI.symm ▸ hM).subset hp)
  exact ⟨I ^ n, GlobalClosedModuleDescent.descent (I ^ n) M hn, hf,
    GlobalClosedModuleDescent.descent_isFinitePresentation (I ^ n) M hn,
    ⟨GlobalClosedModuleDescent.pushforwardIso (I ^ n) M hn⟩⟩

/-- Any line twist of a coherent finite-support sheaf is isomorphic to the sheaf. -/
def finiteSupportLineTwistIso (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : X.Modules) [M.IsFinitePresentation] (hM : (support M).Finite)
    {L : X.Modules} (hL : LocallyFreeRankOne L) : ModuleSheafTensor.tensor M L ≅ M := by
  apply Classical.choice
  obtain ⟨I, N, hf, _, ⟨e⟩⟩ := exists_finiteClosed_descent f M hM
  exact ⟨ModuleSheafTensor.congr e.symm (Iso.refl L) ≪≫
    finiteClosedLineTwistIso I.subschemeι f N hL ≪≫ e⟩

/-- Coherent finite-support sheaves have no positive-degree scalar cohomology. -/
theorem finiteSupport_cohomology_subsingleton
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : X.Modules) [M.IsFinitePresentation] (hM : (support M).Finite)
    (n : ℕ) (hn : 0 < n) : Subsingleton (ModuleScalarH f M n) := by
  have := Chow.source_isNoetherian f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨I, N, hf, hN, ⟨e⟩⟩ := exists_finiteClosed_descent f M hM
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ f)
  have : Subsingleton (ModuleScalarH (I.subschemeι ≫ f) N n) :=
    affine_moduleH_subsingleton N n hn
  exact (((moduleScalarHFunctor f n).mapIso e.symm).toLinearEquiv.trans
    (closedPushforwardScalarHEquiv I.subschemeι N f n)).injective.subsingleton

end FLT.Mazur.FCurve

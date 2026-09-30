/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentClosedReduction
public import FLT.Mazur.CoherentFiltration
public import FLT.Mazur.CoherentSupportedDecomposition

/-!
# Ideal-power filtrations with annihilated factors

The reversed chain of ideal-action images terminates at zero for a coherent
sheaf supported in the ideal's zero locus. Its actual cokernels are killed by
the ideal, as follows by lifting affine sections through the quotient maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}}

/-- Affine ideal annihilation implies annihilation by the actual ideal stalk. -/
theorem IdealKilled.stalk {I : X.IdealSheafData} {M : X.Modules} (hM : IdealKilled I M)
    (x : X) (r : X.presheaf.stalk x) (hr : r ∈ AnnihilatorSubsheaf.stalkIdeal I x)
    (m : M.presheaf.stalk x) : r • m = 0 := by
  obtain ⟨U, _, hx, n, rfl⟩ :=
    AnnihilatorSubsheaf.exists_affine_germ_le M x m ⊤ trivial
  have hm := (AnnihilatorSubsheaf.mem_stalk_annihilated I M x U hx
    (M.presheaf.germ U.1 x hx n)).mpr (fun a ha ↦ by
      erw [← M.val.germ_smul]
      rw [hM U a ha n]
      exact map_zero _)
  exact hm r hr

/-- At an integral closed generic point, killed sheaves satisfy the original stalk hypothesis. -/
theorem IdealKilled.generic_stalk {I : X.IdealSheafData} [IsIntegral I.subscheme]
    {M : X.Modules} (hM : IdealKilled I M) :
    CoherentGenericIdealEmbedding.StalkAnnihilated M
      (I.subschemeι (genericPoint I.subscheme)) := by
  intro r hr m
  apply hM.stalk _ r _ m
  rwa [CoherentClosedReduction.generic_stalkIdeal]

section Local

variable [IsLocallyNoetherian X] (I : X.IdealSheafData) (M : X.Modules)
  [M.IsFinitePresentation]

/-- The adjacent map in the descending chain of actual ideal-power images. -/
abbrev powerStep (n : ℕ) : power I (n + 1) M ⟶ power I n M :=
  transition I M (Nat.le_succ n)

instance powerStep_mono (n : ℕ) : Mono (powerStep I M n) :=
  mono_of_mono_fac (transition_comp I M (Nat.le_succ n))

/-- Multiplication by the ideal on one power factors through the next power. -/
def powerStepFactor (n : ℕ) : power I 1 (power I n M) ⟶ power I (n + 1) M :=
  (nestedPowerIso I n 1 M).hom

@[reassoc]
lemma powerStepFactor_comp (n : ℕ) :
    powerStepFactor I M n ≫ powerStep I M n = inclusion (I ^ 1) (power I n M) := by
  apply (cancel_mono (inclusion (I ^ n) M)).mp
  rw [Category.assoc, transition_comp]
  exact (nestedPowerIso_comp I n 1 M)

/-- The actual adjacent cokernel is killed by the ideal on every affine open. -/
theorem idealKilled_powerStep_cokernel (n : ℕ) :
    IdealKilled I (cokernel (powerStep I M n)) := by
  have := coherent_cokernel (powerStep I M n)
  intro U r hr q
  obtain ⟨m, rfl⟩ := affine_epi_surjective (cokernel.π (powerStep I M n)) U q
  have hm : r • m ∈ LinearMap.range
      ((inclusion (I ^ 1) (power I n M)).val.app (op U.1)).hom := by
    rw [inclusion_range, pow_one]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  obtain ⟨a, ha⟩ := hm
  rw [← Hom.app_smul, ← ha]
  have hf := congrArg (fun f ↦ f.app U.1 a) (powerStepFactor_comp I M n)
  change (powerStep I M n).app U.1 ((powerStepFactor I M n).app U.1 a) = _ at hf
  change (cokernel.π (powerStep I M n)).app U.1
    ((inclusion (I ^ 1) (power I n M)).app U.1 a) = 0
  rw [← hf]
  exact congrArg (fun f ↦ f.app U.1 ((powerStepFactor I M n).app U.1 a))
    (cokernel.condition (powerStep I M n))

/-- The finite reversed chain, before choosing an exponent at which it vanishes. -/
def powerChain (n k : ℕ) (hk : k ≤ n) :
    CoherentChain (IdealKilled I) (power I n M) (power I k M) := by
  induction hk using Nat.decreasingInduction with
  | self => exact .nil inferInstance (Iso.refl _)
  | of_succ k hk ih =>
    exact .snoc (ShortComplex.cokernelSequence (powerStep I M k))
      (coherent_cokernelSequence (powerStep I M k)) ih (idealKilled_powerStep_cokernel I M k)

/-- The zeroth ideal power is canonically the original ambient sheaf. -/
def powerZeroIso : power I 0 M ≅ M := by
  have : IsIso (inclusion (I ^ 0) M) := by
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    infer_instance
  exact asIso (inclusion (I ^ 0) M)

end Local

variable [IsNoetherian X] (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]

/-- Construct an ideal-power filtration with killed, coherent factors. -/
def idealPowerFiltration (hM : support M ⊆ I.support) :
    CoherentFiltration (IdealKilled I) M := by
  let n := (exists_isZero_power I M hM).choose
  have hn := (exists_isZero_power I M hM).choose_spec
  exact ⟨power I n M, hn, (powerChain I M n 0 (Nat.zero_le n)).transport (powerZeroIso I M)⟩

/-- The same construction records the support bound on each of its factors. -/
def supportedIdealPowerFiltration (hM : support M ⊆ I.support) :
    CoherentFiltration (fun Q ↦ IdealKilled I Q ∧ support Q ⊆ support M) M := by
  let c := idealPowerFiltration I M hM
  exact ⟨c.initial, c.initial_zero, c.chain.boundFactors (support M) (Set.Subset.refl _)⟩

end FLT.Mazur.FCurve.CoherentDevissage

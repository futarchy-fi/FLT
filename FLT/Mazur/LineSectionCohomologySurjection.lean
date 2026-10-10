/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTwistTransitionExact
public import FLT.Mazur.FiniteSupportEulerCharacteristic
public import FLT.Mazur.CartierTensorRank

/-!
# Transferring cohomology vanishing along a nonzero line section

A nonzero section on an integral proper curve makes every line-twist
transition injective with finite-support cokernel. Its maps on positive
cohomology are therefore surjective. In particular an acyclic line remains
acyclic after tensoring with any line having a nonzero section.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.LineSectionTwistSystem

open ModuleSheafTensor ModuleLineBundleTensorPullback CoherentDevissage
open FLT.Mazur.GenericIdealInjection

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f]

/-- A nonzero section gives an injective transition for every line coefficient. -/
theorem lineStep_mono {M L : X.Modules} (hM : LocallyFreeRankOne M)
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) (n : ℕ) :
    Mono (step M s n) := by
  have := step_isIso_on_generatorOpen M s n
  have := stalk_isIso_of_restrict (step M s n) (sectionGeneratorOpen L s)
    (genericPoint X) (genericPoint_mem_sectionGeneratorOpen hL s hs)
  exact mono_of_generic_mono_of_line_embedding (hM.tensor (hL.tensorPower n))
    (𝟙 _) (step M s n)

/-- Positive cohomology maps of line transitions are surjective on an integral curve. -/
theorem lineStep_cohomology_surjective (hd : topologicalKrullDim X ≤ 1)
    {M L : X.Modules} (hM : LocallyFreeRankOne M) (hL : LocallyFreeRankOne L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (n q : ℕ) (hq : 0 < q) :
    Function.Surjective (moduleScalarHMap f (step M s n) q) := by
  have := Chow.source_isNoetherian f
  have := hM.isFinitePresentation
  have := (hM.tensor (hL.tensorPower n)).isFinitePresentation
  have := (hM.tensor (hL.tensorPower (n + 1))).isFinitePresentation
  let a := step M s n
  have := lineStep_mono hM hL s hs n
  have := coherent_cokernel a
  have hS := coherent_cokernelSequence a
  have hfin := step_cokernel_finiteSupport hd M hL s hs n
  have : Subsingleton (ModuleScalarH f (cokernel a) q) :=
    finiteSupport_cohomology_subsingleton f (cokernel a) hfin q hq
  have he := moduleScalarH_exact₂ (ShortComplex.cokernelSequence a)
    (moduleToSheaf_shortExact hS.shortExact) f q
  intro x
  apply (he x).mp
  change moduleScalarHMap f (cokernel.π a) q x = 0
  exact Subsingleton.elim _ _

/-- A line with a nonzero section preserves vanishing after tensoring an acyclic line. -/
theorem tensor_cohomology_vanishing_of_section (hd : topologicalKrullDim X ≤ 1)
    {M L : X.Modules} (hM : LocallyFreeRankOne M) (hL : LocallyFreeRankOne L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (q : ℕ) (hq : 0 < q)
    [Subsingleton (ModuleScalarH f M q)] :
    Subsingleton (ModuleScalarH f (tensor M L) q) := by
  let e₀ : tensor M (tensorPower L 0) ≅ M := rightUnitor M
  let e₁ : tensor M (tensorPower L 1) ≅ tensor M L :=
    congr (Iso.refl M) (rightUnitor L)
  let c₀ : ModuleScalarH f (tensor M (tensorPower L 0)) q ≃ₗ[k] ModuleScalarH f M q :=
    ((moduleScalarHFunctor f q).mapIso e₀).toLinearEquiv
  let c₁ : ModuleScalarH f (tensor M (tensorPower L 1)) q ≃ₗ[k]
      ModuleScalarH f (tensor M L) q := ((moduleScalarHFunctor f q).mapIso e₁).toLinearEquiv
  have : Subsingleton (ModuleScalarH f (tensor M (tensorPower L 0)) q) :=
    c₀.injective.subsingleton
  have : Subsingleton (ModuleScalarH f (tensor M (tensorPower L 1)) q) :=
    (lineStep_cohomology_surjective f hd hM hL s hs 0 q hq).subsingleton
  exact c₁.symm.injective.subsingleton

end FLT.Mazur.FCurve.LineSectionTwistSystem

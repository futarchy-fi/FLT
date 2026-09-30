/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowDirectImageComparison
public import FLT.Mazur.ProjectiveCoherentCohomology

/-!
# Finiteness and vanishing for the Chow coefficient

The selected Chow power has finite field-linear cohomology by its closed
projective embedding. The scalar comparison transports finiteness to its
coherent direct image, and relative composition transports positive higher
image vanishing. The exponent and both acyclicity proofs are constructed,
not hypotheses of the target statement in Stacks, Tag 02O5.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.ProjectiveSpace
open FLT.Mazur.ProjectiveSpace.LocalizationDegree

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The scalar map on the Chow modification agrees with its projective presentation. -/
lemma graphStructureScalars_eq :
    structureScalarMap (graphClosureπ f ≫ f) =
      (graphProjectiveImmersion f).appTop.hom.comp
        (constantSection k (Fin (graphProjectiveDimension f + 1)) ⊤) := by
  rw [← graphProjectiveImmersion_baseProjection f]
  simp only [structureScalarMap, Scheme.Hom.comp_appTop, ← Category.assoc]
  rw [CommRingCat.hom_comp, projectiveBaseScalars_eq]

/-- Every Chow line power has finite cohomology with its specified field action. -/
theorem graphLineBundlePower_scalarH_finite (n q : ℕ) :
    Module.Finite k (ModuleScalarH (graphClosureπ f ≫ f) (graphLineBundlePower f n) q) := by
  let := graphLineBundlePower_isFinitePresentation f n
  change @Module.Finite k (ModuleH (graphLineBundlePower f n) q) _ _
    (Module.compHom _ (structureScalarMap (graphClosureπ f ≫ f)))
  rw [graphStructureScalars_eq]
  exact closedSubscheme_coherent_moduleH_finite k _ (graphProjectiveImmersion f)
    (graphLineBundlePower f n) q

/-- Finiteness transports through the field-linear acyclic comparison. -/
theorem chowAcyclicWitness_scalarH_finite (q : ℕ) :
    Module.Finite k (ModuleScalarH f (chowAcyclicWitness f) q) := by
  let := graphLineBundlePower_scalarH_finite f (chowAcyclicExponent f) q
  exact Module.Finite.equiv (chowScalarHEquiv f q).symm

/-- Relative Leray transports the simultaneous Serre vanishing to the Chow witness. -/
theorem chowAcyclicWitness_acyclic : ModulePushforwardAcyclic f (chowAcyclicWitness f) := by
  intro q
  exact ((chowAcyclicExponent_spec f).2 q).of_iso (chowHigherImageIso f (q + 1))

/-- The Chow target: one power gives a coherent, acyclic witness with finite scalar cohomology. -/
theorem exists_chowPower_finite_acyclic :
    ∃ n : ℕ,
      ModulePushforwardAcyclic (graphClosureπ f) (graphLineBundlePower f n) ∧
      ModulePushforwardAcyclic (graphClosureπ f ≫ f) (graphLineBundlePower f n) ∧
      (graphPowerPushforward f n).IsFinitePresentation ∧
      ModulePushforwardAcyclic f (graphPowerPushforward f n) ∧
      ∀ q : ℕ, Module.Finite k (ModuleScalarH f (graphPowerPushforward f n) q) :=
  ⟨chowAcyclicExponent f, (chowAcyclicExponent_spec f).1,
    (chowAcyclicExponent_spec f).2, chowAcyclicWitness_isFinitePresentation f,
    chowAcyclicWitness_acyclic f, chowAcyclicWitness_scalarH_finite f⟩

end FLT.Mazur.Chow

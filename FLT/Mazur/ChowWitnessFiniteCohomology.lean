/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowSimultaneousSerreVanishing
public import FLT.Mazur.ChowWitnessAffineCoherence
public import FLT.Mazur.CoherentCohomologyFinite

/-!
# Finite cohomology of a Chow witness

Projective finiteness applies to every power on the Chow modification with its
specified field structure map. Serre vanishing selects an acyclic power, whose
actual direct image has finite cohomology by the absolute scalar comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.FCurve FLT.Mazur.ProjectiveSpace
open FLT.Mazur.ProjectiveSpace.LocalizationDegree

namespace FLT.Mazur.Chow

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Every Chow line power has finite cohomology over the original field. -/
theorem graphLineBundlePower_hasFiniteCohomology (n : ℕ) :
    HasFiniteCohomology (graphClosureπ f ≫ f) (graphLineBundlePower f n) := by
  let := graphLineBundlePower_isFinitePresentation f n
  have hρ : (graphProjectiveImmersion f).appTop.hom.comp
      (constantSection k (Fin (graphProjectiveDimension f + 1)) ⊤) =
        structureScalarMap (graphClosureπ f ≫ f) := by
    rw [← projectiveBaseScalars_eq]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (baseProjection k _).appTop ≫ (graphProjectiveImmersion f).appTop).hom = _
    rw [← Scheme.Hom.comp_appTop, graphProjectiveImmersion_baseProjection]
    rfl
  intro q
  have hfinite := closedSubscheme_coherent_moduleH_finite k
    (Fin (graphProjectiveDimension f + 1)) (graphProjectiveImmersion f)
    (graphLineBundlePower f n) q
  rw [hρ] at hfinite
  exact hfinite

/-- An actual acyclic Chow power has finite cohomology after direct image. -/
theorem exists_chow_power_finite : ∃ n : ℕ,
    ModulePushforwardAcyclic (graphClosureπ f) (graphLineBundlePower f n) ∧
      HasFiniteCohomology f (graphPowerPushforward f n) := by
  obtain ⟨n, hn, _⟩ := exists_graphLineBundlePower_simultaneously_acyclic f
  refine ⟨n, hn, fun q ↦ ?_⟩
  let := graphLineBundlePower_hasFiniteCohomology f n q
  exact Module.Finite.equiv
    (acyclicPushforwardScalarHEquiv (graphClosureπ f) (graphLineBundlePower f n) hn f q).symm

end FLT.Mazur.Chow

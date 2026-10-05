/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineBaseLineBundle
public import FLT.Mazur.ChowWitnessAffineCoherence
public import FLT.Mazur.PrincipalSectionExtension
public import FLT.Mazur.RelativeSerreVanishing
public import FLT.Mazur.RingCohomologyFinitePushforward

/-!
# Acyclic Chow powers over a Noetherian affine base

The same line has two actual projective presentations. A common Serre
bound gives acyclicity for both maps. Projective finiteness then transfers
finite base-ring cohomology to its direct image. Coherence of that direct
image is a separate obligation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.FCurve FLT.Mazur.ProjectiveSpace
open FLT.Mazur.ProjectiveSpace.LocalizationDegree

namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat} [IsNoetherianRing R] {X : Scheme} (f : X ⟶ Spec R)
  [IsProper f]

/-- One bound makes every later power acyclic for both projections. -/
theorem graphLineBundlePower_eventually_simultaneously_acyclic :
    ∃ N : ℕ, ∀ n ≥ N,
      ModulePushforwardAcyclic (graphClosureπ f) (graphLineBundlePower f n) ∧
      ModulePushforwardAcyclic (graphClosureπ f ≫ f) (graphLineBundlePower f n) := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨N, hN⟩ := relativeVeryAmple_eventually_acyclic (graphClosureπ f)
    (graphLineBundle f) (graphLineBundle_relativeVeryAmple f)
  obtain ⟨M, hM⟩ := relativeVeryAmple_eventually_acyclic (graphClosureπ f ≫ f)
    (graphLineBundle f) (graphLineBundle_absoluteVeryAmple f)
  exact ⟨max N M, fun n hn ↦
    ⟨hN n (le_trans (le_max_left _ _) hn), hM n (le_trans (le_max_right _ _) hn)⟩⟩

/-- A base-ring map canonically induced by the actual structure morphism. -/
def baseCohomologyScalars : R →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom

/-- The projective and structural scalar maps on the modification coincide. -/
lemma graphProjectiveScalars_eq :
    (graphProjectiveImmersion f).appTop.hom.comp
        (constantSection R (Fin (graphProjectiveDimension f + 1)) ⊤) =
      (graphClosureπ f).appTop.hom.comp (baseCohomologyScalars f) := by
  rw [← projectiveBaseScalars_eq]
  change ((Scheme.ΓSpecIso R).inv ≫
    (baseProjection R _).appTop ≫ (graphProjectiveImmersion f).appTop).hom = _
  rw [← Scheme.Hom.comp_appTop, graphProjectiveImmersion_baseProjection]
  rfl

/-- Every Chow line power has finite cohomology over the original Noetherian ring. -/
theorem graphLineBundlePower_hasFiniteRingCohomology (n : ℕ) :
    HasFiniteRingCohomology
      ((graphClosureπ f).appTop.hom.comp (baseCohomologyScalars f))
      (graphLineBundlePower f n) := by
  let := (graphLineBundlePower_locallyFreeRankOne f n).isFinitePresentation
  rw [← graphProjectiveScalars_eq]
  exact projective_hasFiniteRingCohomology (graphProjectiveImmersion f)
    (graphLineBundlePower f n)

/-- An actual common acyclic power has finite cohomology after direct image. -/
theorem exists_chow_power_ring_finite : ∃ n : ℕ,
    ModulePushforwardAcyclic (graphClosureπ f) (graphLineBundlePower f n) ∧
    ModulePushforwardAcyclic (graphClosureπ f ≫ f) (graphLineBundlePower f n) ∧
    HasFiniteRingCohomology (baseCohomologyScalars f)
      ((Scheme.Modules.pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)) := by
  obtain ⟨N, hN⟩ := graphLineBundlePower_eventually_simultaneously_acyclic f
  exact ⟨N, (hN N le_rfl).1, (hN N le_rfl).2,
    (acyclicPushforward_hasFiniteRingCohomology_iff (graphClosureπ f)
      (graphLineBundlePower f N) (hN N le_rfl).1 (baseCohomologyScalars f)).mpr
        (graphLineBundlePower_hasFiniteRingCohomology f N)⟩

end FLT.Mazur.Chow.AffineBase

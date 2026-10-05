/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineBasePropernessCriterion
public import FLT.Mazur.CoefficientImmersionClosedDescent

/-!
# Properness descends to a finite integer coefficient stage

The affine-base Chow modification reduces properness to closedness of its
constructed immersion in a proper projective product. Closedness descends
through the coefficient inverse limit. Thus properness of the original-ring
base change holds at a single finite coefficient enlargement, uniformly.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open FLT.Mazur.Chow.AffineBase

universe u

namespace FLT.Mazur.Approximation

/-- Properness of a separated finite-type coefficient model descends from the
original ring to one finite coefficient enlargement (Stacks 081F in this system). -/
theorem exists_coefficient_isProper {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of S₀))
    [IsSeparated q] [QuasiCompact q] [LocallyOfFiniteType q]
    (hq : IsProper (pullback.snd q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      IsProper (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) := by
  let : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing ℤ S₀
  have : QuasiCompact (graphClosureToProduct q ≫ (chartData q).projectiveProductProjection) := by
    rw [graphClosureToProduct_projection]
    infer_instance
  have : QuasiCompact (graphClosureToProduct q) :=
    QuasiCompact.of_comp (graphClosureToProduct q) (chartData q).projectiveProductProjection
  obtain ⟨i, hi⟩ := exists_coefficient_closedImmersion S₀ (graphClosureπ q ≫ q)
    (chartData q).projectiveProductProjection (graphClosureToProduct q)
    (graphClosureToProduct_projection q)
    ((graph_baseChange_isProper_iff q _).mp hq)
  exact ⟨i, (graph_baseChange_isProper_iff q _).mpr hi⟩

/-- The uniform universal-closedness assertion needed by the coefficient model. -/
theorem exists_coefficient_universallyClosed {A : Type u} [CommRing A]
    (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of S₀))
    [IsSeparated q] [QuasiCompact q] [LocallyOfFinitePresentation q]
    (hq : IsProper (pullback.snd q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      UniversallyClosed (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) := by
  obtain ⟨i, hi⟩ := exists_coefficient_isProper S₀ q hq
  exact ⟨i, inferInstance⟩

end FLT.Mazur.Approximation

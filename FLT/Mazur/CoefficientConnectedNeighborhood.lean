/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientOpenNeighborhood
public import FLT.Mazur.GeometricallyConnectedLocus

/-!
# Capturing the geometrically connected locus at a coefficient stage

A cartesian recovery with geometrically connected fibers puts the entire
original base image in the fiber locus. If that locus is open, the existing
coefficient-limit argument supplies a finite stage with geometrically connected
fibers. Openness remains an explicit geometric hypothesis here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Openness of the actual fiber locus suffices for finite-stage connectedness descent. -/
theorem exists_coefficient_geometricallyConnected_of_isOpen_locus
    {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {X Y : Scheme.{u}} {p : X ⟶ Spec (.of A)} {q : Y ⟶ Spec (.of S₀)}
    {f : X ⟶ Y} (h : IsPullback f p q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
    [GeometricallyConnected p] (ho : IsOpen (geometricallyConnectedLocus q)) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      GeometricallyConnected (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) := by
  let U : (Spec (.of S₀)).Opens := ⟨geometricallyConnectedLocus q, ho⟩
  have hU : Spec.map (CommRingCat.ofHom S₀.val.toRingHom) ⁻¹ᵁ U = ⊤ := by
    apply top_unique
    intro x _
    exact range_subset_geometricallyConnectedLocus h ⟨x, rfl⟩
  exact exists_coefficient_property_of_open_neighborhood S₀ q U hU
    @GeometricallyConnected ((geometricallyConnected_restrict_iff q U).mpr Set.Subset.rfl)

end FLT.Mazur.Approximation

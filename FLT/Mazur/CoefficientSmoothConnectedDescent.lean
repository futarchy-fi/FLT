/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientConnectedNeighborhood
public import FLT.Mazur.ProperSmoothConnectedFiberOpen

/-!
# Finite-stage connectedness for proper smooth pointed models

Actual openness supplies the neighborhood needed by coefficient descent.
No openness or fiber-function comparison remains as an input hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation

/-- A proper smooth pointed coefficient model acquires connected fibers at a finite stage. -/
theorem exists_coefficient_geometricallyConnected_of_proper_smooth
    {A : Type} [CommRing A] (S₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ S₀]
    {X Y : Scheme.{0}} {p : X ⟶ Spec (.of A)} {q : Y ⟶ Spec (.of S₀)}
    {f : X ⟶ Y} (h : IsPullback f p q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
    [GeometricallyConnected p] [IsProper q] [Smooth q]
    (t : Spec (.of S₀) ⟶ Y) (ht : t ≫ q = 𝟙 _) :
    ∃ i : (CoefficientStage S₀)ᵒᵖ,
      GeometricallyConnected (pullback.snd q ((coefficientSpectrumToInitial S₀).app i)) := by
  let _ : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing ℤ S₀
  exact exists_coefficient_geometricallyConnected_of_isOpen_locus S₀ h
    (isOpen_proper_smooth_connectedFiberLocus q t ht)

end FLT.Mazur.Approximation

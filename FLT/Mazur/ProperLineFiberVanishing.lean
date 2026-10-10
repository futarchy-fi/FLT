/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechResidueVanishing
public import FLT.Mazur.FiberCohomologyTensorExactness
public import FLT.Mazur.CanonicalLineSectionBaseChange

/-!
# Relative vanishing from actual residue fibers of a proper flat line family

For a proper flat family over a Noetherian affine base, positive acyclicity on
each actual residue-algebra fiber implies positive acyclicity on the family.
The line may vary: no fixed very ample presentation or global Serre bound is
assumed. Finite projective sections and canonical universal base change follow.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechCoefficients

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The actual pulled-back line on the spectrum of the structural ring's residue field. -/
abbrev residueAlgebraFiberLine (z : PrimeSpectrum Γ(S, ⊤)) :=
  (pullback (Limits.pullback.fst f
    (AffineBaseChangeCoefficients.baseMap S z.asIdeal.ResidueField))).obj L

variable (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
  Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

include hL hV in
/-- Actual residue-fiber acyclicity implies relative positive acyclicity. -/
theorem positive_vanishing_of_residue_fibers (n : ℕ) : Subsingleton (ModuleH L (n + 1)) := by
  let _ := hL.isFinitePresentation
  let _ := Chow.source_isNoetherian (f ≫ S.isoSpec.hom)
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  obtain ⟨ι, hι, U, hU⟩ := IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)
  let _ : Finite ι := hι
  let _ := Fintype.ofFinite ι
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  apply proper_line_vanishing_of_residue_exact f L hL
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) hU _ n
  intro z k
  exact coefficient_exact_of_geometric_vanishing (f := f) L
    (fun i ↦ (U i).1) (fun i ↦ (U i).2) hU z.asIdeal.ResidueField (hV z) k

include hL hV in
/-- The module of sections is finite projective from fiberwise vanishing alone. -/
theorem projective_sections_of_residue_fibers :
    Module.Projective Γ(S, ⊤) (baseSections L f.appTop.hom ⊤) :=
  proper_sections_projective f L hL (positive_flat_of_vanishing f L
    (positive_vanishing_of_residue_fibers f L hL hV))

include hL hV in
/-- The canonical section map is bijective for every affine base change. -/
theorem canonical_bijective_of_residue_fibers {P T : Scheme.{0}} [IsAffine T]
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g) :
    Function.Bijective (globalComparison h L) := by
  let _ := Chow.source_isNoetherian (f ≫ S.isoSpec.hom)
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  exact globalComparison_bijective f L hL (positive_flat_of_vanishing f L
    (positive_vanishing_of_residue_fibers f L hL hV)) h

include hL hV in
/-- Positive vanishing from residue fibers survives arbitrary affine base change. -/
theorem baseChange_vanishing_of_residue_fibers {P T : Scheme.{0}} [IsAffine T]
    {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (h : IsPullback p q f g) (n : ℕ) :
    Subsingleton (ModuleH ((pullback p).obj L) (n + 1)) := by
  let _ := Chow.source_isNoetherian (f ≫ S.isoSpec.hom)
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  exact acyclic_pullback_positive h L hL
    (positive_vanishing_of_residue_fibers f L hL hV) n

end FLT.Mazur.LineSectionBaseChange

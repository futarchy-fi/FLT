/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicLineSectionBaseChange
public import FLT.Mazur.IncreasingCechAffineGeneric
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Finite projective sections of cohomologically flat proper lines

Properness gives finite sections over a Noetherian affine base. Combined with
the bounded Cech flatness theorem, this proves projectivity, principal local
freeness, and locally constant rank for the actual section module.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechCoefficients IncreasingCechCartesian

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] (L : X.Modules)

/-- Proper coherent global sections are finite with their original affine-base scalars. -/
theorem proper_sections_finite [L.IsFinitePresentation] :
    Module.Finite Γ(S, ⊤) (baseSections L f.appTop.hom ⊤) := by
  have hh := AffineBase.proper_coherent_hasFiniteRingCohomology (f ≫ S.isoSpec.hom) L 0
  rw [affinePresentation_scalars] at hh
  let _ := hh
  exact Module.Finite.equiv (ringHZeroBaseSections L f.appTop.hom)

variable [Flat f] (hL : LocallyFreeRankOne L)
  (hH : ∀ n, Module.Flat Γ(S, ⊤) (ModuleRingH f.appTop.hom L (n + 1)))

include hL hH in
/-- Finite projectivity is a consequence of properness and cohomological flatness. -/
theorem proper_sections_projective :
    Module.Projective Γ(S, ⊤) (baseSections L f.appTop.hom ⊤) := by
  let _ := hL.isFinitePresentation
  let _ := Chow.source_isNoetherian (f ≫ S.isoSpec.hom)
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  let _ := proper_sections_finite f L
  let _ := Module.finitePresentation_of_finite Γ(S, ⊤) (baseSections L f.appTop.hom ⊤)
  let _ := sections_flat f L hL hH
  exact Module.Flat.projective_of_finitePresentation

include hL hH in
/-- Around each prime, the actual section module is free on a principal neighborhood. -/
theorem proper_sections_free_neighborhood (x : PrimeSpectrum Γ(S, ⊤)) :
    ∃ r ∉ x.asIdeal, Module.Free (Localization.Away r)
      (LocalizedModule.Away r (baseSections L f.appTop.hom ⊤)) := by
  let M := baseSections L f.appTop.hom ⊤
  let _ := hL.isFinitePresentation
  let _ := proper_sections_finite f L
  let _ := Module.finitePresentation_of_finite Γ(S, ⊤) M
  let _ := proper_sections_projective f L hL hH
  let _ : Module.Free (Localization.AtPrime x.asIdeal)
      (LocalizedModule.AtPrime x.asIdeal M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨r, hr, hf⟩

include hL hH in
/-- The rank of actual proper sections is locally constant on the varying affine base. -/
theorem proper_sections_rank_locallyConstant :
    IsLocallyConstant (Module.rankAtStalk (R := Γ(S, ⊤)) (baseSections L f.appTop.hom ⊤)) := by
  let _ := hL.isFinitePresentation
  let _ := proper_sections_finite f L
  let _ := Module.finitePresentation_of_finite Γ(S, ⊤) (baseSections L f.appTop.hom ⊤)
  let _ := proper_sections_projective f L hL hH
  exact Module.isLocallyConstant_rankAtStalk

include hL in
/-- Positive cohomology vanishing is sufficient for finite projectivity of line sections. -/
theorem proper_acyclic_sections_projective (hV : ∀ n, Subsingleton (ModuleH L (n + 1))) :
    Module.Projective Γ(S, ⊤) (baseSections L f.appTop.hom ⊤) :=
  proper_sections_projective f L hL (positive_flat_of_vanishing f L hV)

end FLT.Mazur.LineSectionBaseChange

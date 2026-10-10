/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundedFlatFiberVanishing
public import FLT.Mazur.ProperLineSectionProjective

/-!
# Residue coefficient detection for actual sheaf cohomology

Apply the bounded-flat descending criterion to the actual increasing Cech
complex. For proper flat line families over Noetherian affine bases, both
term flatness and cohomology finiteness follow from geometry.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechScalars
open FCurve Chow

variable {X : Scheme.{0}} [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  {R : Type} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  [∀ n, Module.Finite R (ModuleRingH ρ M (n + 1))]

omit [Finite ι] in
include hU hCover in
/-- Finiteness of actual cohomology gives finiteness of the adjacent quotient model. -/
theorem positive_quotient_finite (n : ℕ) :
    Module.Finite R ((baseD M U ρ (n + 1)).ker ⧸
      (baseD M U ρ n).range.comap (baseD M U ρ (n + 1)).ker.subtype) :=
  Module.Finite.equiv ((affineRingCohomologyEquiv M U hU hCover ρ (n + 1)).symm.trans
    (basePositiveHomologyEquiv M U ρ n))

variable [∀ n, Module.Flat R (BaseTerm M U ρ n)]
  (hres : ∀ (p : PrimeSpectrum R) n,
    Function.Exact ((baseD M U ρ n).lTensor p.asIdeal.ResidueField)
      ((baseD M U ρ (n + 1)).lTensor p.asIdeal.ResidueField))

include hU hCover hres in
/-- Residue-field exactness of the actual complex kills actual positive sheaf cohomology. -/
theorem ringH_subsingleton_of_residue_exact (n : ℕ) :
    Subsingleton (ModuleRingH ρ M (n + 1)) := by
  let _ := Fintype.ofFinite ι
  let _ (n : ℕ) := positive_quotient_finite M U hU hCover ρ n
  let _ := BoundedFlatFiberVanishing.positive_homology_subsingleton
    (BaseTerm M U ρ) (baseD M U ρ) (baseD_comp M U ρ)
    (Fintype.card ι) (baseTerm_subsingleton M U ρ) hres n
  let _ : Subsingleton (BaseHomology M U ρ (n + 1)) :=
    (basePositiveHomologyEquiv M U ρ n).injective.subsingleton
  let e : BaseHomology M U ρ (n + 1) ≃ₗ[R] ModuleRingH ρ M (n + 1) :=
    affineRingCohomologyEquiv M U hU hCover ρ (n + 1)
  exact e.symm.injective.subsingleton

end FLT.Mazur.IncreasingCechScalars

namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechScalars IncreasingCechCartesian

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [X.IsSeparated]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  (hres : ∀ (p : PrimeSpectrum Γ(S, ⊤)) n,
    Function.Exact ((baseD L U f.appTop.hom n).lTensor p.asIdeal.ResidueField)
      ((baseD L U f.appTop.hom (n + 1)).lTensor p.asIdeal.ResidueField))

include hL hU hCover hres in
/-- Proper flat line families require only residue exactness, not assumed relative vanishing. -/
theorem proper_line_vanishing_of_residue_exact (n : ℕ) :
    Subsingleton (ModuleH L (n + 1)) := by
  let _ := hL.isFinitePresentation
  let _ (n : ℕ) := FlatLineSectionTerms.term_flat f L hL U hU n
  have hfin (n : ℕ) : Module.Finite Γ(S, ⊤) (ModuleRingH f.appTop.hom L (n + 1)) := by
    have hh := AffineBase.proper_coherent_hasFiniteRingCohomology (f ≫ S.isoSpec.hom) L (n + 1)
    rwa [affinePresentation_scalars] at hh
  let _ := hfin
  exact ringH_subsingleton_of_residue_exact L U hU hCover f.appTop.hom hres n

end FLT.Mazur.LineSectionBaseChange

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundedFlatAcyclicNeighborhood
public import FLT.Mazur.ProperLineAcyclicLocus

/-!
# Universal acyclic neighborhoods for proper flat varying lines

One positive-acyclic residue fiber produces a principal neighborhood where
actual positive sheaf cohomology vanishes after every coefficient-algebra
extension. The algebra may be nonflat, nonreduced, or non-Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechScalars IncreasingCechCoefficients IncreasingCechCartesian

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- Around one acyclic fiber, every coefficient algebra has zero actual positive cohomology. -/
theorem exists_principal_universal_positive_vanishing (z : PrimeSpectrum Γ(S, ⊤))
    (hz : ∀ n, Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1))) :
    ∃ r ∉ z.asIdeal, ∀ (B : Type) [CommRing B] [Algebra Γ(S, ⊤) B]
      [Algebra (Localization.Away r) B] [IsScalarTower Γ(S, ⊤) (Localization.Away r) B],
      ∀ n, Subsingleton (ModuleH
        ((pullback (Limits.pullback.fst f (AffineBaseChangeCoefficients.baseMap S B))).obj L)
          (n + 1)) := by
  let _ := hL.isFinitePresentation
  let _ := Chow.source_isNoetherian (f ≫ S.isoSpec.hom)
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  obtain ⟨ι, hι, U, hU⟩ := IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)
  let _ : Finite ι := hι
  let _ := Fintype.ofFinite ι
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let V := fun i ↦ (U i).1
  have hV : ∀ i, IsAffineOpen (V i) := fun i ↦ (U i).2
  let _ (n : ℕ) := FlatLineSectionTerms.term_flat f L hL V hV n
  have hfin (n : ℕ) : Module.Finite Γ(S, ⊤) (ModuleRingH f.appTop.hom L (n + 1)) := by
    have hh := AffineBase.proper_coherent_hasFiniteRingCohomology (f ≫ S.isoSpec.hom) L (n + 1)
    rwa [affinePresentation_scalars] at hh
  let _ := hfin
  let _ (n : ℕ) := positive_quotient_finite L V hV hU f.appTop.hom n
  have hres := (coefficient_exact_iff_geometric_vanishing L V hV hU
    z.asIdeal.ResidueField).mpr hz
  obtain ⟨r, hr, ht⟩ := BoundedFlatVanishingStalks.exists_principal_universally_acyclic
    (BaseTerm L V f.appTop.hom) (baseD L V f.appTop.hom) (baseD_comp L V f.appTop.hom)
    (Fintype.card ι) (baseTerm_subsingleton L V f.appTop.hom) z hres
  refine ⟨r, hr, fun B _ _ _ _ ↦ ?_⟩
  exact (coefficient_exact_iff_geometric_vanishing L V hV hU B).mp (ht B)

include hL in
/-- In particular, the actual line over a principal neighborhood is positive-acyclic. -/
theorem exists_principal_positive_vanishing (z : PrimeSpectrum Γ(S, ⊤))
    (hz : ∀ n, Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1))) :
    ∃ r ∉ z.asIdeal, ∀ n, Subsingleton (ModuleH
      ((pullback (Limits.pullback.fst f
        (AffineBaseChangeCoefficients.baseMap S (Localization.Away r)))).obj L) (n + 1)) := by
  obtain ⟨r, hr, hV⟩ := exists_principal_universal_positive_vanishing f L hL z hz
  exact ⟨r, hr, hV (Localization.Away r)⟩

end FLT.Mazur.LineSectionBaseChange

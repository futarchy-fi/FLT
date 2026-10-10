/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundedFlatAcyclicOpen
public import FLT.Mazur.FiberCohomologyTensorCriterion
public import FLT.Mazur.ProperLineFiberVanishing

/-!
# Openness of positive fiber-cohomology vanishing for a varying proper line

A proper flat line family over an affine Noetherian base has an actual open
where all positive residue-fiber cohomology vanishes. Finite coherent
cohomology and the bounded flat Cech complex construct the open; vanishing
is not assumed globally, and the line bundle may vary with the parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow IncreasingCechScalars IncreasingCechCoefficients IncreasingCechCartesian

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- The actual positive residue-fiber vanishing condition is open for a varying line bundle. -/
theorem isOpen_properLineAcyclicLocus :
    IsOpen {z : PrimeSpectrum Γ(S, ⊤) | ∀ n,
      Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1))} := by
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
  have ho := BoundedFlatVanishingStalks.isOpen_residue_acyclic (BaseTerm L V f.appTop.hom)
    (baseD L V f.appTop.hom) (baseD_comp L V f.appTop.hom)
    (Fintype.card ι) (baseTerm_subsingleton L V f.appTop.hom)
  convert ho using 1
  ext z
  exact (coefficient_exact_iff_geometric_vanishing L V hV hU z.asIdeal.ResidueField).symm

/-- The intrinsic coefficient open defined by actual fiber cohomology. -/
def properLineAcyclicCoefficientOpen : Opens (PrimeSpectrum Γ(S, ⊤)) :=
  ⟨{z | ∀ n, Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1))},
    isOpen_properLineAcyclicLocus f L hL⟩

/-- Membership has no auxiliary cover, homology model, or finite presentation choice. -/
lemma mem_properLineAcyclicCoefficientOpen (z : PrimeSpectrum Γ(S, ⊤)) :
    z ∈ properLineAcyclicCoefficientOpen f L hL ↔ ∀ n,
      Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)) := Iff.rfl

/-- The actual geometric open in the original affine parameter scheme. -/
def properLineAcyclicOpen : S.Opens :=
  S.isoSpec.hom ⁻¹ᵁ properLineAcyclicCoefficientOpen f L hL

/-- Geometric membership is precisely original residue-algebra fiber vanishing. -/
lemma mem_properLineAcyclicOpen (s : S) :
    s ∈ properLineAcyclicOpen f L hL ↔ ∀ n,
      Subsingleton (ModuleH (residueAlgebraFiberLine f L (S.isoSpec.hom s)) (n + 1)) := Iff.rfl

/-- Each acyclic fiber has a principal neighborhood of acyclic fibers in the original base. -/
theorem exists_principal_properLineAcyclic (z : PrimeSpectrum Γ(S, ⊤))
    (hz : ∀ n, Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1))) :
    ∃ r ∉ z.asIdeal, PrimeSpectrum.basicOpen r ≤ properLineAcyclicCoefficientOpen f L hL := by
  have hz' : z ∈ properLineAcyclicCoefficientOpen f L hL := hz
  obtain ⟨V, ⟨_, ⟨r, rfl⟩, rfl⟩, hr, hV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hz'
      (properLineAcyclicCoefficientOpen f L hL).isOpen
  exact ⟨r, hr, hV⟩

end FLT.Mazur.LineSectionBaseChange

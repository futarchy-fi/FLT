/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationExcessFrames
public import FLT.Mazur.EquivalenceRelationCompleteScalarFiber
public import FLT.Mazur.SchemeFiniteGroupBoundaryCompleteness

/-!
# Boundary nilpotence is emptiness of the actual excess-frame scheme

Base change the original excess-frame scheme along the unchanged scalar boundary.
The resulting scheme is empty exactly when the fixed finite completeness tests
are nilpotent. A point retains both its original boundary prime and larger frame.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples SchemeScalarPrincipalNeighborhood AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction invariantScalarCoordinates
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* Γ(U.toScheme, ⊤)) (κ : R →+* T)

/-- The full excess-frame scheme over the unchanged scalar boundary spectrum. -/
def boundaryExcess : Scheme :=
  pullback (excessProjection n o U ≫ scalarMorphism s) (Spec.map (CommRingCat.ofHom κ))

/-- Emptiness is exactly completeness at every original boundary scalar prime. -/
theorem boundaryExcess_isEmpty_iff : IsEmpty (boundaryExcess n o U s κ) ↔
    ∀ (P : PrimeSpectrum T) (x : U.toScheme),
      scalarMorphism s x = PrimeSpectrum.comap κ P →
        U.ι x ∈ completePointLocus (p := p) (q := q) (Fin n) o := by
  constructor
  · intro h P x hx
    by_contra hc
    have hr : x ∈ Set.range (excessProjection n o U) := by
      rw [excessProjection_range]
      exact hc
    obtain ⟨z, hz⟩ := hr
    have he : (excessProjection n o U ≫ scalarMorphism s) z =
        (Spec.map (CommRingCat.ofHom κ)) P := by
      change scalarMorphism s (excessProjection n o U z) = PrimeSpectrum.comap κ P
      rwa [hz]
    obtain ⟨w, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := excessProjection n o U ≫ scalarMorphism s)
      (g := Spec.map (CommRingCat.ofHom κ)) z P he
    exact h.false w
  · intro h
    refine ⟨fun w ↦ ?_⟩
    let z := pullback.fst (excessProjection n o U ≫ scalarMorphism s)
      (Spec.map (CommRingCat.ofHom κ)) w
    let P := pullback.snd (excessProjection n o U ≫ scalarMorphism s)
      (Spec.map (CommRingCat.ofHom κ)) w
    have he : scalarMorphism s (excessProjection n o U z) = PrimeSpectrum.comap κ P :=
      congrArg (fun f ↦ f w) (pullback.condition
        (f := excessProjection n o U ≫ scalarMorphism s)
        (g := Spec.map (CommRingCat.ofHom κ)))
    have hz := Set.mem_range_self (f := excessProjection n o U) z
    rw [excessProjection_range] at hz
    exact hz (h P _ he)

attribute [local irreducible] boundaryExcess boundaryProduct boundaryCoordinate

variable (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
variable (σ : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))

/-- Fixed support functions vanish nilpotently precisely when no larger boundary frame exists. -/
theorem boundary_tests_nilpotent_iff_excess_empty :
    (∀ b ∈ completeAffineOrbitTests e (Fin n) o U hU,
      IsNilpotent (boundaryCoordinate σ κ b)) ↔
        IsEmpty (boundaryExcess n o U (invariantScalarCoordinates ρ σ) κ) := by
  rw [boundaryExcess_isEmpty_iff]
  exact (all_scalar_fibers_subset_iff_boundary_nilpotent ρ
    (U.ι ⁻¹' completePointLocus (p := p) (q := q) (Fin n) o)
    (completeChart_isClosed (Fin n) o U) (completeChart_stable e (Fin n) o U hU) σ κ).symm

/-- An actual excess point gives a fixed support function that fails nilpotence. -/
theorem exists_boundary_test_not_nilpotent
    (w : boundaryExcess n o U (invariantScalarCoordinates ρ σ) κ) :
    ∃ b ∈ completeAffineOrbitTests e (Fin n) o U hU,
      ¬ IsNilpotent (boundaryCoordinate σ κ b) := by
  by_contra h
  push Not at h
  exact ((boundary_tests_nilpotent_iff_excess_empty n o U κ e hU σ).mp h).false w

end FLT.Mazur.EquivalenceRelationNormalizedFrames

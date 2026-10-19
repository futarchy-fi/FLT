/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenRelationFunctions
public import FLT.Mazur.SchemeScalarMinimalEndpoint
public import FLT.Mazur.SchemeFiniteTargetOpenRestriction

/-!
# Original invariant scalar primes reached by finite endpoint geometry

The invariant inclusion on the prescribed orbit domain is injective. On an
affine source domain every minimal prime of that same invariant section ring
therefore has a minimal source endpoint. No own-image scalar ring is substituted.
For a Noetherian source the full relation is finite near this endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeScalarPrincipalNeighborhood SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val
local notation "Ω" => (invariantSheaf e).obj.obj (op W)

/-- The actual original invariant inclusion in the full open-source coordinates. -/
def orbitScalarCoordinates : Ω →+* Γ((E).toScheme, ⊤) :=
  (E).topIso.inv.hom.comp ((invariantInclusion e).hom.app (op W)).hom

/-- These coordinates are precisely the existing invariant function pullbacks. -/
theorem orbitScalarCoordinates_apply (t : Ω) :
    orbitScalarCoordinates e W t = (orbitFunctions e W t).val := rfl

/-- Injectivity is constructed from the original equalizer, without geometric coverage input. -/
theorem orbitScalarCoordinates_injective : Function.Injective (orbitScalarCoordinates e W) := by
  intro a b h
  apply invariantSection_ext e W
  exact (E).topIso.symm.commRingCatIsoToRingEquiv.injective h

/-- Every prescribed minimal scalar prime has a minimal endpoint in the unchanged source open. -/
theorem exists_minimal_scalar_endpoint (hW : IsAffineOpen E)
    (P : PrimeSpectrum Ω) (hP : P.asIdeal ∈ minimalPrimes Ω) :
    let _ : IsAffine (E).toScheme := hW
    ∃ x : (E).toScheme, scalarMorphism (orbitScalarCoordinates e W) x = P ∧
      ((E).toScheme.isoSpec.hom x).asIdeal ∈ minimalPrimes Γ((E).toScheme, ⊤) := by
  let _ : IsAffine (E).toScheme := hW
  exact exists_minimal_endpoint_of_injective _ (orbitScalarCoordinates_injective e W) P hP

variable [IsLocallyNoetherian A.left] [LocallyOfFinitePresentation p.left]
  [LocallyQuasiFinite p.left] [IsSeparated p.left] [QuasiCompact p.left]

/-- Minimal original scalar primes are reached in the whole original finite relation locus. -/
theorem exists_minimal_scalar_finite_endpoint (hW : IsAffineOpen E)
    (P : PrimeSpectrum Ω) (hP : P.asIdeal ∈ minimalPrimes Ω) :
    ∃ x : (E).toScheme, scalarMorphism (orbitScalarCoordinates e W) x = P ∧
      (E).ι x ∈ finiteTargetOpen p.left := by
  let _ : IsAffine (E).toScheme := hW
  obtain ⟨x, hx, hf⟩ := exists_finite_endpoint_of_injective
    (orbitScalarCoordinates e W) (p.left ∣_ E) (orbitScalarCoordinates_injective e W) P hP
  rw [finiteTargetOpen_restrict] at hf
  exact ⟨x, hx, hf⟩

end FLT.Mazur.RelativeRelationOrbit

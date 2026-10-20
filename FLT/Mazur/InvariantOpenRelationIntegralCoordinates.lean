/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRelationIntegralCoordinates
public import FLT.Mazur.RelativeRelationMinimalScalarEndpoints
public import FLT.Mazur.InvariantOpenRelationEquivalence

/-!
# Monic equations over the unchanged orbit-open scalars

Characteristic coefficients on the full restricted relation descend to the
original invariant sheaf, rather than to a replacement scalar ring. A finite
basis for the entire restricted relation constructs integral source coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Module Polynomial
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram AffineRelationCharpoly SchemeFunctionGroundChange
attribute [local instance] sectionAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))
  (es : CategoryTheory.EquivalenceRelation p.left q.left)
include es
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "p₀" => (fst p E).left
local notation "q₀" => (snd p q E (pullOpen_preimage_eq e W)).left
local notation "σ" => orbitScalarCoordinates e W
attribute [local irreducible] invariantSheaf orbitScalarCoordinates invariantInclusion
  sourceSheaf orbitFunctions relationCharpoly
  AffineCartesianCharpoly.sectionCharpoly schemeEquivalence
variable [hA : IsAffine (pullOpen e W).val.toScheme]
  [hD : IsAffine (InvariantOpenRelationDiagram.relation p (pullOpen e W).val).left]
  {ι : Type*} [Finite ι]
include hA hD

/-- The characteristic equation has coefficients in the original orbit-open section ring. -/
theorem exists_orbitScalar_monic_equation :
    let _ := (p₀).appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ((source E).left, ⊤) Γ((relation p E).left, ⊤))
      (s : Γ((E).toScheme, ⊤)),
      ∃ P : Polynomial Ω, P.Monic ∧ P.eval₂ σ s = 0 := by
  let _ := (p₀).appTop.hom.toAlgebra
  let _ : IsAffine (source E).left := hA
  dsimp only
  intro basis s
  let er := schemeEquivalence p q es E (pullOpen_preimage_eq e W)
  let P := relationCharpoly p₀ q₀ basis s
  have hl : P ∈ Polynomial.lifts σ := by
    rw [lifts_iff_coeff_lifts]
    intro n
    let t : AlgHom.equalizer (sectionMap (fst p E))
        (sectionMap (snd p q E (pullOpen_preimage_eq e W))) :=
      ⟨P.coeff n, relationCharpoly_invariant p₀ q₀ er basis s n⟩
    refine ⟨(orbitFunctions e W).symm t, ?_⟩
    rw [orbitScalarCoordinates_apply]
    exact congrArg Subtype.val ((orbitFunctions e W).apply_symm_apply t)
  obtain ⟨Q, hQ⟩ := (mem_lifts _).mp hl
  have he := relationCharpoly_equation p₀ q₀ er basis s
  refine ⟨Q, Polynomial.monic_of_injective (orbitScalarCoordinates_injective e W) ?_, ?_⟩
  · rw [hQ]
    exact he.1
  · rw [← eval_map, hQ]
    exact he.2

/-- Finite free original relation coordinates make the unchanged scalar inclusion integral. -/
theorem orbitScalarCoordinates_integral_of_basis :
    let _ := (p₀).appTop.hom.toAlgebra
    Basis ι Γ((source E).left, ⊤) Γ((relation p E).left, ⊤) → (σ).IsIntegral := by
  let _ := (p₀).appTop.hom.toAlgebra
  dsimp only
  intro basis s
  exact exists_orbitScalar_monic_equation e W es basis s

/-- Finite type upgrades the constructed integral inclusion to scalar module finiteness. -/
theorem orbitScalarCoordinates_finite_of_basis (hft : (σ).FiniteType) :
    let _ := (p₀).appTop.hom.toAlgebra
    Basis ι Γ((source E).left, ⊤) Γ((relation p E).left, ⊤) → (σ).Finite := by
  let _ := (p₀).appTop.hom.toAlgebra
  dsimp only
  intro basis
  exact (orbitScalarCoordinates_integral_of_basis e W es basis).to_finite hft

end FLT.Mazur.RelativeRelationOrbit

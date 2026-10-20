/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectiveRelationIntegralCoordinates
public import FLT.Mazur.RelativeRelationMinimalScalarEndpoints
public import FLT.Mazur.InvariantOpenRelationEquivalence

/-!
# Monic equations over the unchanged orbit-open scalars

Characteristic coefficients on the full restricted relation descend to the
original invariant sheaf, rather than to a replacement scalar ring. Finite
projectivity of the entire restricted relation constructs integral source coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Module Polynomial
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeFunctionGroundChange
open SchemeEffectiveEpiSections FiniteProjectiveRelationIntegralCoordinates
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
  sourceSheaf orbitFunctions schemeEquivalence
variable [hA : IsAffine (pullOpen e W).val.toScheme]
  [hD : IsAffine (InvariantOpenRelationDiagram.relation p (pullOpen e W).val).left]
include hA hD

/-- The characteristic equation has coefficients in the original orbit-open section ring. -/
theorem exists_orbitScalar_monic_equation_of_projective :
    let _ := (p₀).appTop.hom.toAlgebra
    Module.Finite Γ((source E).left, ⊤) Γ((relation p E).left, ⊤) →
    Module.Projective Γ((source E).left, ⊤) Γ((relation p E).left, ⊤) →
    ∀ s : Γ((E).toScheme, ⊤),
      ∃ P : Polynomial Ω, P.Monic ∧ P.eval₂ σ s = 0 := by
  let _ := (p₀).appTop.hom.toAlgebra
  let _ : IsAffine (source E).left := hA
  dsimp only
  intro hf hp s
  let er := schemeEquivalence p q es E (pullOpen_preimage_eq e W)
  obtain ⟨Q, hm, hz⟩ := exists_monic_invariant_polynomial p₀ q₀ er hf hp s
  let P := Q.map (compatibleFunctions p₀ q₀).subtype
  have hi (n : ℕ) : (p₀).appTop (P.coeff n) = (q₀).appTop (P.coeff n) := by
    have ht := (Q.coeff n).property
    change (p₀).appTop (Q.coeff n).val = (q₀).appTop (Q.coeff n).val at ht
    simpa only [P, coeff_map, Subring.subtype_apply] using ht
  have hl : P ∈ Polynomial.lifts σ := by
    rw [lifts_iff_coeff_lifts]
    intro n
    let t : AlgHom.equalizer (sectionMap (fst p E))
        (sectionMap (snd p q E (pullOpen_preimage_eq e W))) :=
      ⟨P.coeff n, hi n⟩
    refine ⟨(orbitFunctions e W).symm t, ?_⟩
    rw [orbitScalarCoordinates_apply]
    exact congrArg Subtype.val ((orbitFunctions e W).apply_symm_apply t)
  obtain ⟨T, hT⟩ := (mem_lifts _).mp hl
  refine ⟨T, Polynomial.monic_of_injective (orbitScalarCoordinates_injective e W) ?_, ?_⟩
  · rw [hT]
    exact hm.map _
  · rw [← eval_map, hT]
    exact (eval_map ..).trans hz

/-- Finite projective original relation coordinates make the unchanged scalar inclusion integral. -/
theorem orbitScalarCoordinates_integral_of_projective :
    let _ := (p₀).appTop.hom.toAlgebra
    Module.Finite Γ((source E).left, ⊤) Γ((relation p E).left, ⊤) →
    Module.Projective Γ((source E).left, ⊤) Γ((relation p E).left, ⊤) → (σ).IsIntegral := by
  let _ := (p₀).appTop.hom.toAlgebra
  dsimp only
  intro hf hp s
  exact exists_orbitScalar_monic_equation_of_projective e W es hf hp s

/-- Finite type upgrades the constructed integral inclusion to scalar module finiteness. -/
theorem orbitScalarCoordinates_finite_of_projective (hft : (σ).FiniteType) :
    let _ := (p₀).appTop.hom.toAlgebra
    Module.Finite Γ((source E).left, ⊤) Γ((relation p E).left, ⊤) →
    Module.Projective Γ((source E).left, ⊤) Γ((relation p E).left, ⊤) → (σ).Finite := by
  let _ := (p₀).appTop.hom.toAlgebra
  dsimp only
  intro hf hp
  exact (orbitScalarCoordinates_integral_of_projective e W es hf hp).to_finite hft

end FLT.Mazur.RelativeRelationOrbit

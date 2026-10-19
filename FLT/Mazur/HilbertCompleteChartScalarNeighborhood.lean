/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertCompleteChartScalarFibers
public import FLT.Mazur.SchemeFiniteGroupPrincipalQuotient

/-!
# Compatible shrinking at unchanged original scalar primes

For a complete affine chart, a stable neighborhood of one point contains its
whole original scalar fiber. Finiteness constructs an original scalar outside
that same prime whose full principal source lies in the requested neighborhood.
The source principal is affine, stable and complete, retaining all scheme structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
variable (n : ℕ) (o : Fin n)
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ g : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
local notation "j" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
set_option quotPrecheck false
local notation "O" => orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)
local notation "E" => (pullOpen eo O).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op O)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)

local notation "hUO" => normalizedChart_over_orbitImage f hL d V c k n o U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o O U hU hUO
local notation "ρ" => restrictedAction τ U hU
local notation "σ₀" => invariantScalarCoordinates ρ σ
open SchemeScalarPrincipalNeighborhood

variable [IsAffine U.toScheme]

/-- One point suffices on a stable open because the proved scalar fiber is its full orbit. -/
theorem completeChart_scalar_fiber_subset_stable
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (B : U.toScheme.Opens) (hB : ∀ g, (ρ g).hom ⁻¹ᵁ B = B)
    (x : U.toScheme) (hx : x ∈ B) :
    ∀ y : U.toScheme, scalarMorphism σ₀ y = scalarMorphism σ₀ x → y ∈ B := by
  intro y hy
  obtain ⟨g, rfl⟩ :=
    (completeChart_scalar_fiber_iff_orbit f hL d V c k n o U hU hc x y).mp hy.symm
  change x ∈ (ρ g).hom ⁻¹ᵁ B
  rwa [hB]

/-- Construct an original scalar avoiding the prescribed prime and shrinking its whole fiber. -/
theorem completeChart_exists_originalScalar_neighborhood
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (B : U.toScheme.Opens) (hB : ∀ g, (ρ g).hom ⁻¹ᵁ B = B)
    (P : PrimeSpectrum Ω) (x : U.toScheme) (hx : x ∈ B)
    (hxP : scalarMorphism σ₀ x = P) :
    ∃ r : Ω, r ∉ P.asIdeal ∧ U.toScheme.basicOpen (σ₀ r) ≤ B := by
  let _ := completeChart_scalarMorphism_finite f hL d V c k n o U hU hc
  apply exists_scalar_of_closed_fiber σ₀ B P (scalarMorphism σ₀).isClosedMap
  intro y hy
  exact completeChart_scalar_fiber_subset_stable f hL d V c k n o U hU hc B hB x hx y
    (hy.trans hxP.symm)

/-- The constructed shrink remains an affine stable complete chart over the same scalar prime. -/
theorem completeChart_exists_affine_originalScalar_shrink
    (hc : ∀ y ∈ U, y ∈ completePointLocus («p» := p) («q» := q) (Fin n) o)
    (B : U.toScheme.Opens) (hB : ∀ g, (ρ g).hom ⁻¹ᵁ B = B)
    (P : PrimeSpectrum Ω) (x : U.toScheme) (hx : x ∈ B)
    (hxP : scalarMorphism σ₀ x = P) :
    ∃ r : Ω, r ∉ P.asIdeal ∧ U.toScheme.basicOpen (σ₀ r) ≤ B ∧
      IsAffineOpen (U.toScheme.basicOpen (σ₀ r)) ∧
      x ∈ U.toScheme.basicOpen (σ₀ r) ∧
      (∀ g, (ρ g).hom ⁻¹ᵁ U.toScheme.basicOpen (σ₀ r) =
        U.toScheme.basicOpen (σ₀ r)) ∧
      ∀ y : (U.toScheme.basicOpen (σ₀ r)).toScheme,
        U.ι y.val ∈ completePointLocus («p» := p) («q» := q) (Fin n) o := by
  obtain ⟨r, hrP, hrB⟩ :=
    completeChart_exists_originalScalar_neighborhood f hL d V c k n o U hU hc B hB P x hx hxP
  refine ⟨r, hrP, hrB, (isAffineOpen_top U.toScheme).basicOpen _, ?_,
    basicOpen_stable ρ (σ r), fun y ↦ hc y.val.val y.val.property⟩
  rw [← scalarMorphism_preimage]
  change scalarMorphism σ₀ x ∈ PrimeSpectrum.basicOpen r
  rwa [hxP]

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPrescribedMinimalScalarCharts
public import FLT.Mazur.HilbertSubframeOriginalScalars
public import FLT.Mazur.SchemeScalarAvoidanceCover
public import FLT.Mazur.SchemeOriginalScalarOpenCorrections

/-!
# Actual complete-chart scalar fibers over prescribed minimal primes

The existing normalized scalar map factors through the full original source
coordinates. Thus the constructed complete charts collectively reach every
minimal prime of the prescribed scalar ring itself. Each chart keeps its
constructed n; no replacement by its own orbit image is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeOpenEnvelope
open RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsLocallyNoetherian A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "s" => orbitScalarCoordinates eo W

attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  invariantSheaf normalizedOriginalScalarMap

variable (n : ℕ) (o : Fin n)
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ g : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "ρ" => restrictedAction τ U hU
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates ρ σ
local notation "j" => (normalizedFullRelationFirst f hL d V c k n o).resLE E U hUW

omit [IsLocallyNoetherian A.left] [Etale V.hom] in
/-- The chart's source scalar coordinates are the original invariant inclusion pulled back. -/
theorem normalizedSource_scalarCoordinates_factor :
    σ₀ = (j).appTop.hom.comp s := by
  ext r
  change (σ r).val = (j).appTop (s r)
  rw [normalizedOriginalScalarMap_val, orbitScalarCoordinates_apply]

omit [IsLocallyNoetherian A.left] [Etale V.hom] in
/-- The actual scalar morphism retains the prescribed domain, not merely the chart's image. -/
theorem normalizedSource_scalarMorphism_factor :
    scalarMorphism σ₀ = j ≫ scalarMorphism s := by
  rw [normalizedSource_scalarCoordinates_factor, scalarMorphism_comp]

end FLT.Mazur.HilbertChart.AffineRestriction

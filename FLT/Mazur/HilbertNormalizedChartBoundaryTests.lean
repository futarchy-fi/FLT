/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformSourceOriginalSections
public import FLT.Mazur.RelativeRelationEtaleOrbitImageMap
public import FLT.Mazur.EquivalenceRelationBoundaryChartTests

/-!
# Original boundary tests on arbitrary normalized chart domains

The exact boundary coefficient equation can be tested on any original orbit
domain containing the normalized chart. No completeness or saturation of the
chart is needed for this scheme-valued equation.
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
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
variable (n : ℕ) (o : Fin n)
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
attribute [local irreducible] RelativeRelationOrbit.orbitSetoid
  RelativeRelationOrbit.pullOpen
set_option quotPrecheck false
local notation "Wc" w:max => (TopologicalSpace.Opens.map (m).base).obj w
local notation "Ec" w:max => (pullOpen ec (Wc w)).val
local notation "i" => originalBoundarySourceMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence

attribute [local irreducible] normalizedOrbitBoundaryCoefficient normalizedBoundaryChartMap
  normalizedOriginalBoundaryAction normalizedFullRelationAction

/-- Exact boundary coefficients agree on every scheme test over the original boundary. -/
theorem normalizedChart_original_boundary_test
    (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n o) U hU))
    (t : (invariantSheaf ec).obj.obj (op (Wc W)))
    (hv : normalizedBoundaryChartMap f hL d V c k n o U hU v =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
    {T : Scheme} (a : T ⟶ U.toScheme) (b : T ⟶ (Ec W).toScheme)
    (hab : a ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o =
      b ≫ (Ec W).ι ≫ (i).left) :
    a.appTop v.val = b.appTop (orbitFunctions ec (Wc W) t).val := by
  apply InvariantBoundary.boundary_coefficient_test o (i).left U (Ec W) a b hab
    (normalizedOrbitBoundary_domain_le f hL d V c k n o W U hUW)
    v.val (orbitFunctions ec (Wc W) t).val
  simpa only [normalizedBoundaryChartMap, invariantMap_val,
    normalizedOrbitBoundaryCoefficient_val, normalizedOriginalBoundaryInclusion,
    normalizedOriginalBoundaryEndpoint] using congrArg Subtype.val hv

end FLT.Mazur.HilbertChart.AffineRestriction

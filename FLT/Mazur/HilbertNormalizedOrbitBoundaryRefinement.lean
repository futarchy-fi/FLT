/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCoefficients
public import FLT.Mazur.FiniteGroupBoundaryChartRestriction

/-!
# Original orbit-boundary coefficients agree on moving chart refinements

The actual original sheaf section pulls back compatibly to smaller stable
source charts. Every lift restricts to a lift of that same original section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem endpointApp_refinement {X Y : Scheme} (b : X ⟶ Y) (V : Y.Opens)
    (U U' : X.Opens) (h : U' ≤ U) (hU : U ≤ b ⁻¹ᵁ V) (hU' : U' ≤ b ⁻¹ᵁ V)
    (t : Γ(V.toScheme, ⊤)) :
    (X.homOfLE h).appTop ((b.resLE V U hU).appTop t) =
      (b.resLE V U' hU').appTop t := by
  change (((b.resLE V U hU).appTop ≫ (X.homOfLE h).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, Scheme.Hom.map_resLE]

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
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

variable (U' : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U' = U') (h : U' ≤ U)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- An original orbit-domain boundary section has the same coefficient on every refinement. -/
theorem normalizedOrbitBoundaryCoefficient_refinement :
    boundaryInvariantRestriction ρ τ j hj U hU U' hU' h
        (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t) =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U' hU' (h.trans hUW) t := by
  apply Subtype.ext
  simp only [boundaryInvariantRestriction_val, normalizedOrbitBoundaryCoefficient_val]
  exact endpointApp_refinement b Uc (j ⁻¹ᵁ U) (j ⁻¹ᵁ U') ((j).preimage_mono h)
    (normalizedOrbitBoundary_domain_le f hL d V c k n o W U hUW)
    (normalizedOrbitBoundary_domain_le f hL d V c k n o W U' (h.trans hUW))
    (orbitFunctions ec Wc t).val

/-- Restricting a chosen lift still lifts the same arbitrary original boundary section. -/
theorem normalizedOrbitBoundaryLift_refinement
    (a : invariantCoordinates (restrictedAction τ U hU))
    (ha : normalizedBoundaryChartMap f hL d V c k n o U hU a =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t) :
    normalizedBoundaryChartMap f hL d V c k n o U' hU'
        (FiniteGroupOpenRelation.invariantRestriction τ U hU U' hU' h a) =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U' hU' (h.trans hUW) t := by
  calc
    _ = boundaryInvariantRestriction ρ τ j hj U hU U' hU' h
        (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t) :=
      boundary_chart_lift_restriction ρ τ j hj U hU U' hU' h a _ ha
    _ = _ := normalizedOrbitBoundaryCoefficient_refinement
      f hL d V c k n o W U hU hUW U' hU' h t

end FLT.Mazur.HilbertChart.AffineRestriction

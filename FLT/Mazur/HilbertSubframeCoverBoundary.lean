/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeBoundaryLifts
public import FLT.Mazur.EquivalenceRelationBoundarySubframeCover

/-!
# Detecting exact original boundary lifts on subframe covers

Surjectivity of the actual selected chart map makes its entire boundary a
faithfully flat cover. Exact original boundary coefficients can therefore be
checked after selected pullback, for arbitrary target charts and all residue
characteristics.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
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

variable (m' : ℕ) (a : Fin m') (ι : Fin m' ↪ Fin n)
  (U' : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin m'),
    (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ U' = U')
  (h : U ≤ subframeMap (fullRelationSchemeEquivalence f hL d V c k) o a ι ⁻¹ᵁ U')
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

variable [Surjective (subframeRefinementMap
  (fullRelationSchemeEquivalence f hL d V c k) o a ι U U' h)]

/-- A selected cover detects exact lifting of the unchanged original boundary coefficient. -/
theorem normalizedOrbitBoundaryLift_subframeCover_iff
    (w : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k m' a) U' hU')) :
    normalizedBoundaryChartMap f hL d V c k m' a U' hU' w =
      normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t ↔
    ((j) ∣_ U).appTop ((subframeRefinementMap e o a ι U U' h).appTop w.val) =
      (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t).val := by
  rw [Subtype.ext_iff]
  simp only [normalizedOrbitBoundaryCoefficient_val]
  apply InvariantBoundary.subframeBoundaryRefinement_lift_iff e o a ι i z r s hr hs
    U U' h Uc (pullOpen_preimage_eq ec Wc)
    (normalizedOrbitBoundary_domain_le f hL d V c k n o W U hUW)
    (normalizedOrbitBoundary_domain_le f hL d V c k m' a W U' hU'W)
    (orbitFunctions ec Wc t).val _ w.val
  have ht := (orbitFunctions ec Wc t).property
  change ((r).resLE Uc _ le_rfl).appTop (orbitFunctions ec Wc t).val =
    ((s).resLE Uc _ (pullOpen_preimage_eq ec Wc).le).appTop
      (orbitFunctions ec Wc t).val at ht
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using ht

end FLT.Mazur.HilbertChart.AffineRestriction

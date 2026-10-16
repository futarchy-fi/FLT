/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryActionGeometry
public import FLT.Mazur.HilbertBoundaryRelationTests
public import FLT.Mazur.HilbertNormalizedFrameAction

/-!
# The moving normalized action on the original Hilbert boundary

The original Cartesian closed relation constructs an action on the exact
pullback boundary of normalized full-relation frames. Both the moving first
endpoint and the original closed transition arrow are retained as scheme maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
variable (n : ℕ) (o : Fin n)

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  relation fst snd

/-- The full original closed boundary pulled back along the normalized first endpoint. -/
def normalizedOriginalBoundary : Scheme :=
  InvariantBoundary.boundary («p» := p) («q» := q) (Fin n) o i

/-- The unchanged normalized frame inclusion of the original boundary. -/
def normalizedOriginalBoundaryInclusion : normalizedOriginalBoundary f hL d V c k n o ⟶
    normalizedFullRelationFrames f hL d V c k n o :=
  InvariantBoundary.inclusion (Fin n) o i

/-- The original closed first endpoint of a boundary frame. -/
def normalizedOriginalBoundaryEndpoint :
    normalizedOriginalBoundary f hL d V c k n o ⟶ (B).left :=
  InvariantBoundary.endpoint (Fin n) o i

/-- The inclusion retains the entire original closed scheme structure. -/
instance normalizedOriginalBoundaryInclusion_closed :
    IsClosedImmersion (normalizedOriginalBoundaryInclusion f hL d V c k n o) :=
  InvariantBoundary.inclusion_isClosedImmersion (Fin n) o i

/-- The normalized moving permutation acts on the actual original closed boundary. -/
def normalizedOriginalBoundaryAction :
    Equiv.Perm (Fin n) →* Aut (normalizedOriginalBoundary f hL d V c k n o) :=
  InvariantBoundary.action e (Fin n) o i z r s hr hs

/-- Each boundary permutation retains its whole original closed relation arrow. -/
def normalizedOriginalBoundaryTransition (σ : Equiv.Perm (Fin n)) :
    normalizedOriginalBoundary f hL d V c k n o ⟶ (C).left :=
  InvariantBoundary.transition (Fin n) o i z r hr σ

/-- Exact equivariance with the original moving action on the ambient normalized source. -/
@[reassoc] theorem normalizedOriginalBoundaryAction_inclusion (σ : Equiv.Perm (Fin n)) :
    (normalizedOriginalBoundaryAction f hL d V c k n o σ).hom ≫
      normalizedOriginalBoundaryInclusion f hL d V c k n o =
    normalizedOriginalBoundaryInclusion f hL d V c k n o ≫
      (normalizedFullRelationAction f hL d V c k n o σ).hom :=
  InvariantBoundary.action_inclusion e (Fin n) o i z r s hr hs σ

omit [Etale V.hom] in
/-- Closed transition coefficients are exactly those of the original normalized action arrow. -/
@[reassoc] theorem normalizedOriginalBoundaryTransition_arrow (σ : Equiv.Perm (Fin n)) :
    normalizedOriginalBoundaryTransition f hL d V c k n o σ ≫ z =
      normalizedOriginalBoundaryInclusion f hL d V c k n o ≫
        actionArrow (Fin n) o σ :=
  InvariantBoundary.transition_arrow (Fin n) o i z r hr σ

/-- The closed first endpoint moves along the original closed relation's second endpoint. -/
@[reassoc] theorem normalizedOriginalBoundaryAction_endpoint (σ : Equiv.Perm (Fin n)) :
    (normalizedOriginalBoundaryAction f hL d V c k n o σ).hom ≫
      normalizedOriginalBoundaryEndpoint f hL d V c k n o =
    normalizedOriginalBoundaryTransition f hL d V c k n o σ ≫ s :=
  InvariantBoundary.map_endpoint e (Fin n) o i z r s hr hs σ

/-- Boundary transport is an exact scheme pullback of the original moving action. -/
theorem normalizedOriginalBoundaryAction_isPullback (σ : Equiv.Perm (Fin n)) :
    IsPullback (normalizedOriginalBoundaryAction f hL d V c k n o σ).hom
      (normalizedOriginalBoundaryInclusion f hL d V c k n o)
      (normalizedOriginalBoundaryInclusion f hL d V c k n o)
      (normalizedFullRelationAction f hL d V c k n o σ).hom :=
  InvariantBoundary.action_isPullback e (Fin n) o i z r s hr hs σ

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedBoundaryAction
public import FLT.Mazur.HilbertNormalizedStableAffine
public import FLT.Mazur.EquivalenceRelationBoundaryCoefficients

/-!
# Actual moving affine charts lift original Hilbert boundary coefficients

Every normalized source point has a stable affine etale neighborhood on which
all original whole-relation boundary functions lift invariantly. The chart map
uses the original closed immersion and moving action. Exhaustiveness for the
whole original relation, and descent to arbitrary orbit domains, remain separate.
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

local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
open FiniteGroupRestriction SchemeFiniteGroupQuotient
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)

/-- The actual invariant coordinate map for the original boundary on a moving source chart. -/
def normalizedBoundaryChartMap :
    invariantCoordinates (restrictedAction τ U hU) →+*
      invariantCoordinates (boundaryOpenAction ρ τ j hj U hU) :=
  invariantMap (boundaryOpenAction ρ τ j hj U hU) (restrictedAction τ U hU)
    (j ∣_ U) (boundaryOpen_equivariant ρ τ j hj U hU)

/-- An original whole-relation boundary function on the exact moving source chart. -/
def normalizedBoundaryChartCoefficient (t : Γ((B).left, ⊤))
    (ht : (r).appTop t = (s).appTop t) :
    invariantCoordinates (boundaryOpenAction ρ τ j hj U hU) :=
  InvariantBoundary.openInvariantCoefficient e (Fin n) o i z r s hr hs t ht U hU

/-- Every original coefficient lifts through the actual chart map on an affine source open. -/
theorem normalizedBoundaryChartCoefficient_lift (ha : IsAffineOpen U)
    (t : Γ((B).left, ⊤)) (ht : (r).appTop t = (s).appTop t) :
    ∃ a, normalizedBoundaryChartMap f hL d V c k n o U hU a =
      normalizedBoundaryChartCoefficient f hL d V c k n o U hU t ht :=
  InvariantBoundary.openInvariantCoefficient_lift e (Fin n) o i z r s hr hs t ht U hU ha

/-- Each normalized point has an actual source chart lifting every original boundary function. -/
theorem exists_normalized_boundary_chart_lifts (x : N) :
    ∃ (U : (N).Opens) (hU : ∀ σ : Equiv.Perm (Fin n), (τ σ).hom ⁻¹ᵁ U = U),
      IsAffineOpen U ∧ x ∈ U ∧
      Etale (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o) ∧
      ∀ (t : Γ((B).left, ⊤)) (ht : (r).appTop t = (s).appTop t),
        ∃ a, normalizedBoundaryChartMap f hL d V c k n o U hU a =
          normalizedBoundaryChartCoefficient f hL d V c k n o U hU t ht := by
  obtain ⟨U, hU, hx, hρ, he⟩ := exists_normalized_stable_affine f hL d V c k n o x
  exact ⟨U, hρ, hU, hx, he,
    normalizedBoundaryChartCoefficient_lift f hL d V c k n o U hρ hU⟩

end FLT.Mazur.HilbertChart.AffineRestriction

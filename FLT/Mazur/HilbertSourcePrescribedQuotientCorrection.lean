/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceInvariantCharacterOrbits
public import FLT.Mazur.EquivalenceRelationExactQuotientCorrectionExtension

/-!
# Original Hilbert correction extensions with a fixed input and fixed finite solution

A prescribed exact finite quotient correction extends to the original ambient
boundary kernel for the same original input. Its restrictions solve every
complete quotient order, keeping the original n and every nilpotent direction.
The required full scalar-fiber completeness remains an independent obligation.
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
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ g : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "α" => restrictedAction τ U hU
local notation "hj" => restrictedAction_hom_ι τ U hU
local notation "j" order => completeQuotientFrameInclusion e (Fin n) o U hU order
local notation "coeff" a:max order:max => completeQuotientCoefficient e (Fin n) o U hU a order
local notation "i" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "hi" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
local notation "β" => FiniteGroupEquivariantPullback.action α ρ τ U.ι i hj hi
local notation "b" => pullback.fst U.ι i
local notation "hb" => FiniteGroupEquivariantPullback.action_fst α ρ τ U.ι i hj hi
attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction

/-- Preserve the original input, boundary, n, and a prescribed exact finite solution together. -/
theorem originalSource_prescribed_exact_quotient_correction
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val)
    (order : ℕ) (z : Γ(completeQuotientFrame e (Fin n) o U hU order, ⊤))
    (hz : (pullback.fst (j order) i).appTop z = 0)
    (he : (SourceRestriction.fst (j order) (j order)).appTop z -
        (SourceRestriction.snd (j order) (j order)).appTop z =
      (SourceRestriction.fst (j order) (j order)).appTop (coeff a order) -
        (SourceRestriction.snd (j order) (j order)).appTop (coeff a order)) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' order = z ∧
      ∀ r : ℕ,
        (pullback.fst (j r) i).appTop (coeff z' r) = 0 ∧
        (SourceRestriction.fst (j r) (j r)).appTop (coeff z' r) -
          (SourceRestriction.snd (j r) (j r)).appTop (coeff z' r) =
        (SourceRestriction.fst (j r) (j r)).appTop (coeff a r) -
          (SourceRestriction.snd (j r) (j r)).appTop (coeff a r) :=
  completeQuotient_exact_correction_all_orders
    e (Fin n) o U hU i ρ hi t a ha order z hz he

end FLT.Mazur.HilbertChart.AffineRestriction

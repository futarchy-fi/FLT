/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceInvariantCharacterOrbits
public import FLT.Mazur.EquivalenceRelationCompleteQuotientCorrections

/-!
# Original Hilbert boundary corrections over complete quotient powers

Construct exact boundary-zero corrections on the finite flat original frame
covers of every complete-orbit quotient power. These retain the original n
and the entire original closed boundary. Extending them to the ambient scalar
fiber still requires containment in these stages and compatible algebraization.
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
  [IsAffine U.toScheme] (order : ℕ)
local notation "S" => completeQuotientFrame e (Fin n) o U hU order
local notation "j" => completeQuotientFrameInclusion e (Fin n) o U hU order
local notation "α" => completeQuotientFrameAction e (Fin n) o U hU order
local notation "hj" => completeQuotientFrameAction_inclusion e (Fin n) o U hU order
local notation "i" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "hi" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
local notation "β" => FiniteGroupEquivariantPullback.action α ρ τ j i hj hi
local notation "b" => pullback.fst j i
local notation "hb" => FiniteGroupEquivariantPullback.action_fst α ρ τ j i hj hi
attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction

/-- Every full positive quotient stage carries actual complete original frames. -/
theorem originalSource_complete_quotient_stage_support :
    Set.range j ⊆ completePointLocus («p» := p) («q» := q) (Fin n) o :=
  completeQuotientFrame_complete e (Fin n) o U hU order

/-- Every original invariant boundary coefficient lifts on the constructed complete stage. -/
theorem originalSource_complete_quotient_boundary_surjective :
    Function.Surjective (invariantMap β α b hb) :=
  completeQuotientFrame_boundary_surjective e (Fin n) o U hU order i ρ hi

/-- A constructed exact boundary correction retains the original two-endpoint discrepancy. -/
theorem originalSource_complete_quotient_boundary_correction
    (t : invariantCoordinates β) (a : Γ(S, ⊤)) (ha : (b).appTop a = t.val) :
    ∃ z : Γ(S, ⊤), (b).appTop z = 0 ∧
      (SourceRestriction.fst j j).appTop z - (SourceRestriction.snd j j).appTop z =
        (SourceRestriction.fst j j).appTop a - (SourceRestriction.snd j j).appTop a :=
  completeQuotientFrame_boundary_correction e (Fin n) o U hU order i ρ hi t a ha

/-- The exact original closed boundary kernel is recovered, with all of its nilpotents. -/
theorem originalSource_complete_quotient_boundary_kernel :
    (RingHom.ker (invariantMap β α b hb)).map
      (let _ := SchemeCoordinateAction.coordinateAction α
       FiniteGroupQuotient.inclusion (Equiv.Perm (Fin n)) Γ(S, ⊤)) =
        RingHom.ker (b).appTop.hom :=
  completeQuotientFrame_boundary_kernel e (Fin n) o U hU order i ρ hi

/-- Original coefficient descent keeps every power of every ideal on the quotient stage. -/
theorem originalSource_complete_quotient_power_iff
    (J : Ideal Γ(completeQuotientStage e (Fin n) o U hU order, ⊤)) (m : ℕ) :
    (J.map (completeQuotientFrameCover e (Fin n) o U hU order).appTop.hom) ^ m = ⊥ ↔
      J ^ m = ⊥ :=
  completeQuotientFrame_power_iff e (Fin n) o U hU order J m

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedFrameAction
public import FLT.Mazur.SchemeRelationDoubleRestriction
public import FLT.Mazur.SchemeRelationGraphOpenEquations
public import FLT.Mazur.FiniteGroupOpenRestriction

/-!
# Actual permutation graphs in the full Hilbert source relation

Every permutation on a stable normalized chart lifts to an original
relation arrow. Hence the full open-pair section equation already implies
all permutation-overlap equations, even on a nonstable usable open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  (n : ℕ) (o : Fin n)
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
open EquivalenceRelationNormalizedFrames

open FiniteGroupRestriction SchemeFiniteGroupQuotient
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "τU" => restrictedAction τ U hU

/-- A permutation graph is an actual arrow into the full two-endpoint original relation. -/
def originalSourceActionRelationArrow (σ : Equiv.Perm (Fin n)) :
    U.toScheme ⟶ SchemeRelationRestriction.doubleDomain p q kS :=
  SchemeRelationRestriction.lift p q kS
    (U.ι ≫ normalizedFullRelationCoordinate f hL d V c k n o (σ.symm o))
    (𝟙 _) (τU σ).hom
    (by rw [Category.assoc, normalizedFullRelationCoordinate_first, Category.id_comp])
    (by rw [Category.assoc, ← normalizedFullRelationAction_first,
      ← Category.assoc, ← restrictedAction_hom_ι, Category.assoc])

/-- The graph retains its unchanged first endpoint. -/
@[reassoc] theorem originalSourceActionRelationArrow_fst (σ : Equiv.Perm (Fin n)) :
    originalSourceActionRelationArrow f hL d V c k n o U hU σ ≫
      SchemeRelationRestriction.fst p q kS = 𝟙 _ :=
  SchemeRelationRestriction.lift_fst _ _ _ _ _ _ _ _

/-- Its independent second endpoint is the actual restricted permutation. -/
@[reassoc] theorem originalSourceActionRelationArrow_snd (σ : Equiv.Perm (Fin n)) :
    originalSourceActionRelationArrow f hL d V c k n o U hU σ ≫
      SchemeRelationRestriction.snd p q kS = (τU σ).hom :=
  SchemeRelationRestriction.lift_snd _ _ _ _ _ _ _ _

/-- Full original open-pair compatibility constructs every permutation-overlap equation. -/
theorem originalSource_pairOpen_action_equation (O : U.toScheme.Opens)
    (v : Γ(O.toScheme, ⊤))
    (he : (pairOpenFirst O (SchemeRelationRestriction.fst p q kS)
      (SchemeRelationRestriction.snd p q kS)).appTop v =
      (pairOpenSecond O (SchemeRelationRestriction.fst p q kS)
        (SchemeRelationRestriction.snd p q kS)).appTop v) (σ : Equiv.Perm (Fin n)) :
    (pairOpenFirst O (𝟙 _) (τU σ).hom).appTop v =
      (pairOpenSecond O (𝟙 _) (τU σ).hom).appTop v :=
  pairOpen_equation_of_relation_graph _ _ _
    (originalSourceActionRelationArrow f hL d V c k n o U hU σ)
    (originalSourceActionRelationArrow_fst f hL d V c k n o U hU σ)
    (originalSourceActionRelationArrow_snd f hL d V c k n o U hU σ) O v he

end FLT.Mazur.HilbertChart.AffineRestriction

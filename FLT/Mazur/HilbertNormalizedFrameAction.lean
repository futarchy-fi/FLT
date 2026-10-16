/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameComparison

/-!
# Endpoint-moving normalized frames for the original Hilbert relation

The actual full Hilbert relation yields a normalized frame scheme and a free
permutation action moving its first endpoint. The original coefficient morphism
is invariant. On complete geometric frames the action realizes every original
relation arrow, with both independent endpoints retained.
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
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  (n : ℕ) (o : Fin n)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
open EquivalenceRelationNormalizedFrames

/-- The actual normalized source formed from the whole original Hilbert relation. -/
def normalizedFullRelationFrames : Scheme := source p q (Fin n) o

/-- The original first endpoint, which the normalized permutation action may move. -/
def normalizedFullRelationFirst : normalizedFullRelationFrames f hL d V c k n o ⟶ A.left :=
  first p q (Fin n) o

/-- Every original relation arrow coordinate is retained on the normalized source. -/
def normalizedFullRelationCoordinate (i : Fin n) :
    normalizedFullRelationFrames f hL d V c k n o ⟶ (relation f hL d V c k).left :=
  coordinate p q (Fin n) o i

/-- The finite permutation action rebases to the newly distinguished original endpoint. -/
def normalizedFullRelationAction :
    Equiv.Perm (Fin n) →* Aut (normalizedFullRelationFrames f hL d V c k n o) :=
  action e (Fin n) o

omit [Etale V.hom] in
/-- Every coordinate still starts at the original first endpoint. -/
@[reassoc] theorem normalizedFullRelationCoordinate_first (i : Fin n) :
    normalizedFullRelationCoordinate f hL d V c k n o i ≫ p =
      normalizedFullRelationFirst f hL d V c k n o := coordinate_first p q (Fin n) o i

omit [Etale V.hom] in
/-- The new first endpoint is an independent original second endpoint. -/
@[reassoc] theorem normalizedFullRelationAction_first (σ : Equiv.Perm (Fin n)) :
    (normalizedFullRelationAction f hL d V c k n o σ).hom ≫
      normalizedFullRelationFirst f hL d V c k n o =
        normalizedFullRelationCoordinate f hL d V c k n o (σ.symm o) ≫ q :=
  actionMap_first e (Fin n) o σ

omit [Etale V.hom] in
/-- Every second endpoint is permuted as an actual original scheme morphism. -/
@[reassoc] theorem normalizedFullRelationAction_second (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (normalizedFullRelationAction f hL d V c k n o σ).hom ≫
      normalizedFullRelationCoordinate f hL d V c k n o i ≫ q =
        normalizedFullRelationCoordinate f hL d V c k n o (σ.symm i) ≫ q :=
  actionMap_second e (Fin n) o σ i

omit [Etale V.hom] in
/-- The unchanged original coefficient morphism is invariant under endpoint-moving permutations. -/
@[reassoc] theorem normalizedFullRelationAction_coefficients (σ : Equiv.Perm (Fin n)) :
    (normalizedFullRelationAction f hL d V c k n o σ).hom ≫
      normalizedFullRelationFirst f hL d V c k n o ≫ A.hom =
        normalizedFullRelationFirst f hL d V c k n o ≫ A.hom :=
  action_coefficients e (Fin n) o A.hom
    ((fst f hL d V c k).w.trans (snd f hL d V c k).w.symm) σ

omit [Etale V.hom] in
/-- The normalized action is free on all nonempty original tests. -/
theorem normalizedFullRelationAction_free {T : Scheme} [Nonempty T]
    (u : T ⟶ normalizedFullRelationFrames f hL d V c k n o) (σ : Equiv.Perm (Fin n))
    (hσ : u ≫ (normalizedFullRelationAction f hL d V c k n o σ).hom = u) : σ = 1 :=
  action_free e (Fin n) o u σ hσ

/-- Complete original geometric frames recover the entire original relation by this action. -/
theorem normalizedFullRelation_geometric_iff {K : Type} [Field K]
    (u v : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k n o)
    (hu : Complete («p» := p) («q» := q) (Fin n) o u)
    (hv : Complete («p» := p) («q» := q) (Fin n) o v) :
    (∃ a : Spec (.of K) ⟶ (relation f hL d V c k).left,
      a ≫ p = u ≫ normalizedFullRelationFirst f hL d V c k n o ∧
      a ≫ q = v ≫ normalizedFullRelationFirst f hL d V c k n o) ↔
      ∃! σ : Equiv.Perm (Fin n),
        u ≫ (normalizedFullRelationAction f hL d V c k n o σ).hom = v :=
  original_arrow_iff_unique_permutation e (Fin n) o u v hu hv

end FLT.Mazur.HilbertChart.AffineRestriction

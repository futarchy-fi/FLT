/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedAffineNeighborhood
public import FLT.Mazur.EquivalenceRelationNormalizedCompleteRelation

/-!
# Complete finite orbits in the original normalized Hilbert relation

Completeness is preserved by the moving action and by every original arrow
between normalized frames of the same size. The open comparison therefore
contains all original arrows with a complete first endpoint. Complete lifts
also have actual stable affine neighborhoods; relation exhaustiveness there
is not asserted.
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

variable (n : ℕ) (o : Fin n) {K : Type} [Field K]

omit [Etale V.hom] in
/-- Completeness is invariant under the original endpoint-moving normalized Hilbert action. -/
theorem normalizedFullRelationAction_complete_iff
    (u : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k n o)
    (σ : Equiv.Perm (Fin n)) :
    Complete (Fin n) o (u ≫ (normalizedFullRelationAction f hL d V c k n o σ).hom) ↔
      Complete (Fin n) o u := action_complete_iff e (Fin n) o u σ

/-- One complete endpoint suffices to retain every full original Hilbert relation arrow. -/
theorem normalizedOriginalAction_complete_first
    (z : Spec (.of K) ⟶ normalizedOriginalRelation f hL d V c k n o)
    (hz : Complete (Fin n) o (z ≫ relationFirst p q (Fin n) o)) :
    ∃ w : Spec (.of K) ⟶ permutationRelation («p» := p) («q» := q) (Fin n) o,
      w ≫ relationComparison e (Fin n) o = z :=
  complete_first_factors_relationComparison e (Fin n) o z hz

/-- Every original geometric endpoint has a complete lift and a stable affine orbit neighborhood. -/
theorem exists_normalized_complete_affine_lift [IsSepClosed K]
    (b : Spec (.of K) ⟶ A.left) :
    ∃ (m : ℕ) (j : Fin m)
      (u : Spec (.of K) ⟶ normalizedFullRelationFrames f hL d V c k m j)
      (U : (source p q (Fin m) j).Opens),
      u ≫ normalizedFullRelationFirst f hL d V c k m j = b ∧
      Complete (Fin m) j u ∧ IsAffineOpen U ∧ frameOrbit e (Fin m) j (u default) ⊆ U ∧
      ∀ σ : Equiv.Perm (Fin m),
        (normalizedFullRelationAction f hL d V c k m j σ).hom ⁻¹ᵁ U = U := by
  obtain ⟨m, j, u, hb, hu⟩ := exists_complete_normalized_lift e b
  obtain ⟨U, hU, horbit, _, hstable⟩ :=
    exists_normalizedFrame_stable_affine f hL d V c k m j (u default) ⊤ (by
      intro x hx
      trivial)
  exact ⟨m, j, u, U, hb, hu, hU, horbit, hstable⟩

end FLT.Mazur.HilbertChart.AffineRestriction

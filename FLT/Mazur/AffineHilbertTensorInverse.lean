/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTensorScalars

/-!
# Actual inversion on glued tensor families

The full original relation inversion acts on matching families even though
an individual principal tensor chart need not be inversion-stable. The action
is involutive, exchanges the two original endpoint maps and preserves scalars.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
/-- The algebra induced by the original source structural morphism. -/
local instance inverseMatchingSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance inverseMatchingTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom


namespace TensorChart
local notation "s" => Over.Hom.left (CategoryTheory.SymmetricRelation.s
  (CategoryTheory.EquivalenceRelation.toSymmetricRelation (equivalence f hL d V c k)))

/-- The original inversion acts on all matching families, using their proved gluing. -/
@[irreducible] def matchingInverse : matchingRing f hL d V c k →+* matchingRing f hL d V c k :=
  (toMatching f hL d V c k).comp (matchingPullback f hL d V c k s)

/-- Inversion of a matching family is the original pullback after reconstructing sections. -/
theorem matchingInverse_global (a : Γ((Z).left, ⊤)) :
    matchingInverse f hL d V c k (toMatching f hL d V c k a) =
      toMatching f hL d V c k ((s).appTop a) := by
  unfold matchingInverse
  change toMatching f hL d V c k
    (matchingPullback f hL d V c k s (toMatching f hL d V c k a)) = _
  rw [matchingPullback_toMatching]

/-- No chart-stability assumption is needed for the involutive action on all matching families. -/
theorem matchingInverse_involutive : Function.Involutive (matchingInverse f hL d V c k) := by
  intro z
  obtain ⟨a, rfl⟩ := (toMatching_bijective f hL d V c k).surjective z
  have h₁ := congrArg (matchingInverse f hL d V c k)
    (matchingInverse_global f hL d V c k a)
  have h₂ := matchingInverse_global f hL d V c k ((s).appTop a)
  refine h₁.trans (h₂.trans ?_)
  have hs : (s) ≫ (s) = 𝟙 (Z).left :=
    congrArg Over.Hom.left (swapIso f hL d V c k).hom_inv_id
  change toMatching f hL d V c k (((s) ≫ (s)).appTop a) = _
  exact congrArg (fun g : (Z).left ⟶ (Z).left ↦
    toMatching f hL d V c k (g.appTop a)) hs

/-- Original inversion interchanges the first endpoint with the second endpoint. -/
theorem matchingInverse_source (a : Γ(A.left, ⊤)) :
    matchingInverse f hL d V c k (matchingSource f hL d V c k a) =
      matchingTest f hL d V c k a := by
  unfold matchingInverse
  change toMatching f hL d V c k
    (matchingPullback f hL d V c k s (matchingSource f hL d V c k a)) = _
  rw [matchingPullback_source]
  have hs : (s) ≫ (p).left = (q).left :=
    congrArg Over.Hom.left (equivalence f hL d V c k).symmetry₁
  rw [hs]
  rfl

/-- Original inversion interchanges the second endpoint with the first endpoint. -/
theorem matchingInverse_test (a : Γ(A.left, ⊤)) :
    matchingInverse f hL d V c k (matchingTest f hL d V c k a) =
      matchingSource f hL d V c k a := by
  unfold matchingInverse
  change toMatching f hL d V c k
    (matchingPullback f hL d V c k s (matchingTest f hL d V c k a)) = _
  rw [matchingPullback_test]
  have hs : (s) ≫ (q).left = (p).left :=
    congrArg Over.Hom.left (equivalence f hL d V c k).symmetry₂
  rw [hs]
  rfl

attribute [local instance] matchingAlgebra

/-- Inversion preserves the actual structural R-algebra on matching coefficient families. -/
def matchingInverseAlgHom : matchingRing f hL d V c k →ₐ[R] matchingRing f hL d V c k := by
  refine ⟨matchingInverse f hL d V c k, ?_⟩
  intro r
  change matchingInverse f hL d V c k (algebraMap R (matchingRing f hL d V c k) r) = _
  rw [← (matchingSourceAlgHom f hL d V c k).commutes r]
  change matchingInverse f hL d V c k
    (matchingSource f hL d V c k (algebraMap R Γ(A.left, ⊤) r)) = _
  rw [matchingInverse_source]
  exact ((matchingTestAlgHom f hL d V c k).commutes r).trans
    ((matchingSourceAlgHom f hL d V c k).commutes r).symm

end TensorChart
end FLT.Mazur.HilbertChart.AffineRestriction

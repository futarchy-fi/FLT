/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedOrbitBoundaryRefinement
public import FLT.Mazur.EquivalenceRelationEqualFrameCorrections

/-!
# Original Hilbert boundary corrections on common affine frame charts

On any actual stable affine normalized chart inside the original orbit domain,
one lift of the original boundary value constructs embedding corrections on all
its stable subcharts simultaneously. Residual and unequal-frame equations are
not replaced by these local same-frame equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

include hU in
/-- Actual original-boundary lifts have simultaneous same-frame embedding corrections. -/
theorem originalEqualFrame_embedding_corrections (ha : IsAffineOpen U)
    {T : Type} (Us : T → (normalizedFullRelationFrames f hL d V c k n o).Opens)
    (hUs : ∀ a σ, (τ σ).hom ⁻¹ᵁ Us a = Us a) (h : ∀ a, Us a ≤ U)
    (u : ∀ a, invariantCoordinates (restrictedAction τ (Us a) (hUs a)))
    (hu : ∀ a, normalizedBoundaryChartMap f hL d V c k n o (Us a) (hUs a) (u a) =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W (Us a) (hUs a)
        ((h a).trans hUW) t) :
    ∃ corr : ∀ a, invariantCoordinates (restrictedAction τ (Us a) (hUs a)),
      (∀ a, ((j) ∣_ Us a).appTop (corr a).val = 0) ∧
      ∀ a b (ι : Fin n ↪ Fin n),
        ((MixedFrames.mixedEmbeddingTestOpen e o o
          (MixedFrames.mixedChartOpen o o (Us a) (Us b)).ι ι).ι ≫
          MixedFrames.mixedChartFirst o o (Us a) (Us b)).appTop (corr a).val -
        ((MixedFrames.mixedEmbeddingTestOpen e o o
          (MixedFrames.mixedChartOpen o o (Us a) (Us b)).ι ι).ι ≫
          MixedFrames.mixedChartSecond o o (Us a) (Us b)).appTop (corr b).val =
        ((MixedFrames.mixedEmbeddingTestOpen e o o
          (MixedFrames.mixedChartOpen o o (Us a) (Us b)).ι ι).ι ≫
          MixedFrames.mixedChartFirst o o (Us a) (Us b)).appTop (u a).val -
        ((MixedFrames.mixedEmbeddingTestOpen e o o
          (MixedFrames.mixedChartOpen o o (Us a) (Us b)).ι ι).ι ≫
          MixedFrames.mixedChartSecond o o (Us a) (Us b)).appTop (u b).val := by
  apply MixedFrames.exists_equalFrame_embedding_corrections e (Fin n) o U hU
    j ρ hj ha Us hUs h
    (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t) u
  intro a
  exact (hu a).trans
    (normalizedOrbitBoundaryCoefficient_refinement f hL d V c k n o W U hU hUW
      (Us a) (hUs a) (h a) t).symm

end FLT.Mazur.HilbertChart.AffineRestriction

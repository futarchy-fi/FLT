/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertLabelResidualLifts

/-!
# Simultaneous corrections across independently labelled source charts

Subtract the constructed common-chart lifts from arbitrary exact boundary lifts.
The resulting one family of boundary-zero corrections solves every full-size
embedding discrepancy at once. Its residual discrepancies are left explicit.
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
/-- Construct one family of exact boundary-zero corrections for all labelled embedding stages. -/
theorem originalLabel_embedding_corrections (ha : IsAffineOpen U)
    {T : Type} (a : T → Fin n)
    (Us : (v : T) → (normalizedFullRelationFrames f hL d V c k n (a v)).Opens)
    (hUs : ∀ v σ,
      (normalizedFullRelationAction f hL d V c k n (a v) σ).hom ⁻¹ᵁ Us v = Us v)
    (h : ∀ v, Us v ≤ labelChange e (Fin n) (a v) o ⁻¹ᵁ U)
    (u : ∀ x, invariantCoordinates
      (restrictedAction (normalizedFullRelationAction f hL d V c k n (a x))
        (Us x) (hUs x)))
    (hu : ∀ x, normalizedBoundaryChartMap f hL d V c k n (a x) (Us x) (hUs x) (u x) =
      normalizedOrbitBoundaryCoefficient f hL d V c k n (a x) W (Us x) (hUs x)
        (normalizedLabelRefinement_domain f hL d V c k n o W U hUW
          (a x) (Us x) (h x)) t) :
    ∃ corr : ∀ x, invariantCoordinates
        (restrictedAction (normalizedFullRelationAction f hL d V c k n (a x))
          (Us x) (hUs x)),
      (∀ x, ((normalizedOriginalBoundaryInclusion f hL d V c k n (a x)) ∣_ Us x).appTop
        (corr x).val = 0) ∧
      ∀ x y (ι : Fin n ↪ Fin n),
        ((MixedFrames.mixedEmbeddingTestOpen e (a x) (a y)
          (MixedFrames.mixedChartOpen (a x) (a y) (Us x) (Us y)).ι ι).ι ≫
          MixedFrames.mixedChartFirst (a x) (a y) (Us x) (Us y)).appTop (corr x).val -
        ((MixedFrames.mixedEmbeddingTestOpen e (a x) (a y)
          (MixedFrames.mixedChartOpen (a x) (a y) (Us x) (Us y)).ι ι).ι ≫
          MixedFrames.mixedChartSecond (a x) (a y) (Us x) (Us y)).appTop (corr y).val =
        ((MixedFrames.mixedEmbeddingTestOpen e (a x) (a y)
          (MixedFrames.mixedChartOpen (a x) (a y) (Us x) (Us y)).ι ι).ι ≫
          MixedFrames.mixedChartFirst (a x) (a y) (Us x) (Us y)).appTop (u x).val -
        ((MixedFrames.mixedEmbeddingTestOpen e (a x) (a y)
          (MixedFrames.mixedChartOpen (a x) (a y) (Us x) (Us y)).ι ι).ι ≫
          MixedFrames.mixedChartSecond (a x) (a y) (Us x) (Us y)).appTop (u y).val := by
  obtain ⟨v, hv, he⟩ := exists_originalLabel_embedding_lifts f hL d V c k n o W U hU hUW
    t ha a Us hUs h
  refine ⟨fun x ↦ u x - v x, fun x ↦ ?_, fun x y ι ↦ ?_⟩
  · have hb := congrArg Subtype.val ((hu x).trans (hv x).symm)
    change ((normalizedOriginalBoundaryInclusion f hL d V c k n (a x)) ∣_ Us x).appTop
      ((u x).val - (v x).val) = 0
    rw [map_sub, sub_eq_zero]
    exact hb
  · have hsub (x : T) : (u x - v x).val = (u x).val - (v x).val := rfl
    rw [hsub, hsub, map_sub, map_sub, he x y ι]
    abel

end FLT.Mazur.HilbertChart.AffineRestriction

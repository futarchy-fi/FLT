/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertLabelBoundaryRefinement
public import FLT.Mazur.HilbertNormalizedBoundarySurjectivity
public import FLT.Mazur.HilbertMixedResidualBranches
public import FLT.Mazur.EquivalenceRelationMixedResidualExtension

/-!
# Original boundary lifts across a family of independently labelled charts

One lift on a stable affine chart supplies a simultaneous family on all labelled
subcharts. Every full-size graph discrepancy vanishes, and the full discrepancy
is exactly the extension of its residual coefficient. Strict subframes and
unrelated common-chart domains are not discharged by this construction.
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

local instance labelResidual_sourceSeparated (a : Fin n) :
    (source p q (Fin n) a).IsSeparated := normalizedFrameSource_separated f hL d V c k n a

include hU in
/-- Common affine geometry constructs exact original lifts across independent labels. -/
theorem exists_originalLabel_embedding_lifts (ha : IsAffineOpen U)
    {T : Type} (a : T → Fin n)
    (Us : (v : T) → (normalizedFullRelationFrames f hL d V c k n (a v)).Opens)
    (hUs : ∀ v σ,
      (normalizedFullRelationAction f hL d V c k n (a v) σ).hom ⁻¹ᵁ Us v = Us v)
    (h : ∀ v, Us v ≤ labelChange e (Fin n) (a v) o ⁻¹ᵁ U) :
    ∃ v : ∀ x, invariantCoordinates
        (restrictedAction (normalizedFullRelationAction f hL d V c k n (a x))
          (Us x) (hUs x)),
      (∀ x, normalizedBoundaryChartMap f hL d V c k n (a x) (Us x) (hUs x) (v x) =
        normalizedOrbitBoundaryCoefficient f hL d V c k n (a x) W (Us x) (hUs x)
          (normalizedLabelRefinement_domain f hL d V c k n o W U hUW
            (a x) (Us x) (h x)) t) ∧
      ∀ x y (ι : Fin n ↪ Fin n),
        ((MixedFrames.mixedEmbeddingTestOpen e (a x) (a y)
          (MixedFrames.mixedChartOpen (a x) (a y) (Us x) (Us y)).ι ι).ι ≫
          MixedFrames.mixedChartFirst (a x) (a y) (Us x) (Us y)).appTop (v x).val =
        ((MixedFrames.mixedEmbeddingTestOpen e (a x) (a y)
          (MixedFrames.mixedChartOpen (a x) (a y) (Us x) (Us y)).ι ι).ι ≫
          MixedFrames.mixedChartSecond (a x) (a y) (Us x) (Us y)).appTop (v y).val := by
  obtain ⟨w, hw⟩ := normalizedBoundaryChartMap_surjective f hL d V c k n o U hU ha
    (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
  refine ⟨fun x ↦ labelInvariantRestriction e (Fin n) o U hU (a x)
    (Us x) (hUs x) (h x) w, fun x ↦ ?_, fun x y ι ↦ ?_⟩
  · exact normalizedOrbitBoundaryLift_labelRefinement f hL d V c k n o W U hU hUW
      (a x) (Us x) (hUs x) (h x) _ t w hw
  · exact MixedFrames.mixedLabelRefinement_branch_equalizes e (Fin n) o U hU
      (a x) (Us x) (hUs x) (h x) (a y) (Us y) (hUs y) (h y) ι w

include hU in
/-- The constructed independently labelled lifts have only the exact residual discrepancy. -/
theorem exists_originalLabel_residual_lifts (ha : IsAffineOpen U)
    {T : Type} (a : T → Fin n)
    (Us : (v : T) → (normalizedFullRelationFrames f hL d V c k n (a v)).Opens)
    (hUs : ∀ v σ,
      (normalizedFullRelationAction f hL d V c k n (a v) σ).hom ⁻¹ᵁ Us v = Us v)
    (h : ∀ v, Us v ≤ labelChange e (Fin n) (a v) o ⁻¹ᵁ U) :
    ∃ v : ∀ x, invariantCoordinates
        (restrictedAction (normalizedFullRelationAction f hL d V c k n (a x))
          (Us x) (hUs x)),
      (∀ x, normalizedBoundaryChartMap f hL d V c k n (a x) (Us x) (hUs x) (v x) =
        normalizedOrbitBoundaryCoefficient f hL d V c k n (a x) W (Us x) (hUs x)
          (normalizedLabelRefinement_domain f hL d V c k n o W U hUW
            (a x) (Us x) (h x)) t) ∧
      ∀ x y,
        let M := MixedFrames.mixedChartOpen (a x) (a y) (Us x) (Us y)
        let err := (MixedFrames.mixedChartFirst (a x) (a y) (Us x) (Us y)).appTop (v x).val -
          (MixedFrames.mixedChartSecond (a x) (a y) (Us x) (Us y)).appTop (v y).val
        err = MixedFrames.mixedResidualSectionExtension e (a x) (a y) M.ι
          ((MixedFrames.mixedResidualTestOpen e (a x) (a y) M.ι).ι.appTop err) := by
  obtain ⟨v, hv, he⟩ := exists_originalLabel_embedding_lifts f hL d V c k n o W U hU hUW
    t ha a Us hUs h
  refine ⟨v, hv, fun x y ↦ ?_⟩
  apply (MixedFrames.mixedResidualSectionExtension_reconstruct e (a x) (a y) _ _ ?_).symm
  intro ι
  rw [map_sub, sub_eq_zero]
  exact he x y ι

end FLT.Mazur.HilbertChart.AffineRestriction

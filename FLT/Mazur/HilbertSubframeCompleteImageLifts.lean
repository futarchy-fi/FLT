/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeCoverBoundary
public import FLT.Mazur.HilbertSubframeLocalizedEmbeddingLifts
public import FLT.Mazur.EquivalenceRelationSubframeImageDescent

/-!
# Geometric exchange vanishing on complete source chart images

An affine stable source chart entirely supported on complete frames supplies
an invariant lift of each original boundary coefficient. Descent constructs a
compatible invariant lift on its strict subframe image; faithful boundary
pullback proves the exact target boundary value. This gives actual local
exchange vanishing in every characteristic on these charts. No complete open
neighborhood is claimed at an arbitrary boundary point.
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
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
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
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
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

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "E" => (pullOpen eo W).val

variable (m' : ℕ) (a : Fin m') (ι : Fin m' ↪ Fin n)
local notation "T" => subframeImageOpen e o a U ι
local notation "hT" => subframeImageOpen_stable e o a U hU ι
local notation "hTW" => subframeImageOpen_le_domain e o a U ι
  (pullOpen eo W).val (pullOpen_preimage_eq eo W) hUW
local notation "hSel" => subframeImage_all_domain e o a U hU ι
local notation "Tinv" => invariantCoordinates (restrictedAction
  (normalizedFullRelationAction f hL d V c k m' a) T hT)
local notation "α" => normalizedBoundaryChartMap f hL d V c k n o U hU
local notation "β" => normalizedBoundaryChartMap f hL d V c k m' a T hT
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
local notation "tS" => normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t
local notation "tT" => normalizedOrbitBoundaryCoefficient f hL d V c k m' a W T hT hTW t
variable (ha : IsAffineOpen U)
  (hc : ∀ y : normalizedFullRelationFrames f hL d V c k n o,
    y ∈ U → y ∈ completePointLocus
      («p» := Over.Hom.left (AffineRestriction.fst f hL d V c k))
      («q» := Over.Hom.left (AffineRestriction.snd f hL d V c k)) (Fin n) o)

include ha hc in
/-- Geometry constructs exact compatible source and strict-image target boundary lifts. -/
theorem originalCompleteSubframeImage_lifts :
    ∃ (u : Sinv) (v : Tinv), α u = tS ∧ β v = tT ∧
      (subframeRefinementMap e o a ι U T (hSel ι)).appTop v.val = u.val := by
  obtain ⟨u, hu⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k n o W U hU hUW t ha
  obtain ⟨v, hv, _⟩ := subframeImageCover_complete_existsUnique e o a U hU ι hc u
  let _ : Surjective (subframeRefinementMap e o a ι U T (hSel ι)) :=
    subframeImageCover_surjective e o a U ι
  refine ⟨u, v, hu, ?_, hv⟩
  apply (normalizedOrbitBoundaryLift_subframeCover_iff f hL d V c k n o W U hU hUW
    m' a ι T hT (hSel ι) hTW t v).mpr
  change (subframeRefinementMap e o a ι U T (hSel ι)).appTop v.val = u.val at hv
  rw [hv]
  exact congrArg Subtype.val hu

include ha hc in
/-- A strict-image lift can be chosen to satisfy every exchange equation without denominators. -/
theorem originalCompleteSubframeImage_exchange_lift (b₀ : Fin n) :
    ∃ v : Tinv, β v = tT ∧ subframeExchangeMap e o a U T hT hSel ι b₀ v = 0 := by
  obtain ⟨u, v, _, hv, huv⟩ := originalCompleteSubframeImage_lifts
    f hL d V c k n o W U hU hUW m' a ι t ha hc
  have he := (subframePullback_invariant_iff e o a U hU T hSel ι v.val).mp
    ⟨u, huv.symm⟩
  refine ⟨v, hv, ?_⟩
  change (subframeRefinementMap e o a (ι.trans (Equiv.swap (ι a) b₀).toEmbedding)
    U T _).appTop v.val - (subframeRefinementMap e o a ι U T _).appTop v.val = 0
  exact sub_eq_zero.mpr (he _)

variable (b₀ : Fin n)
  (M : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))

include ha hc in
/-- All exact lifts on the complete chart image have zero original localized exchange class. -/
theorem originalLocalizedExchangeClass_complete_image_zero (v : Tinv) (hv : β v = tT) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a T hT hTW hSel ι b₀ M v = 0 := by
  obtain ⟨w, hw, he⟩ := originalCompleteSubframeImage_exchange_lift
    f hL d V c k n o W U hU hUW m' a ι t ha hc b₀
  rw [originalLocalizedExchangeClass_zero_iff_lift]
  refine ⟨1, w, ?_, he⟩
  simpa only [OneMemClass.coe_one, map_one, one_mul, hv] using hw

end FLT.Mazur.HilbertChart.AffineRestriction

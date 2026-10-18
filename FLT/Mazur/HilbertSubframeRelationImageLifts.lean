/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeCoverBoundary
public import FLT.Mazur.HilbertSubframeLocalizedEmbeddingLifts
public import FLT.Mazur.EquivalenceRelationSubframeRelationLifts

/-!
# Original exchange vanishing from full-relation source lifts

A full-relation-compatible lift on the larger source chart descends to its
strict image, with exact original boundary and all exchange equations. The
construction does not require a complete source open. Producing such a full
source lift at arbitrary original boundary primes remains a separate task.
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
local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "CS" => SchemeEffectiveEpiSections.compatibleFunctions
  (SchemeRelationRestriction.fst p q kS) (SchemeRelationRestriction.snd p q kS)

/-- A full original source lift constructs an exact strict-image lift without completeness. -/
theorem originalRelationSubframeImage_lifts (u : Sinv) (hu : α u = tS)
    (he : u.val ∈ CS) :
    ∃ v : Tinv, β v = tT ∧
      ∀ κ : Fin m' ↪ Fin n,
        (subframeRefinementMap e o a κ U T (hSel κ)).appTop v.val = u.val := by
  obtain ⟨v, hv, _⟩ := subframe_sourceRelation_existsUnique e o a U hU ι ⟨u.val, he⟩
  let _ : Surjective (subframeRefinementMap e o a ι U T (hSel ι)) :=
    subframeImageCover_surjective e o a U ι
  refine ⟨v, ?_, subframeImageCover_descended_all e o a U hU ι u v hv⟩
  apply (normalizedOrbitBoundaryLift_subframeCover_iff f hL d V c k n o W U hU hUW
    m' a ι T hT (hSel ι) hTW t v).mpr
  change (subframeRefinementMap e o a ι U T (hSel ι)).appTop v.val = u.val at hv
  rw [hv]
  exact congrArg Subtype.val hu

/-- Full-relation source lifts give an exact zero-exchange lift on the actual image. -/
theorem originalRelationSubframeImage_exchange_lift (u : Sinv) (hu : α u = tS)
    (he : u.val ∈ CS) (b₀ : Fin n) :
    ∃ v : Tinv, β v = tT ∧ subframeExchangeMap e o a U T hT hSel ι b₀ v = 0 := by
  obtain ⟨v, hv, hselect⟩ := originalRelationSubframeImage_lifts
    f hL d V c k n o W U hU hUW m' a ι t u hu he
  refine ⟨v, hv, ?_⟩
  change (subframeRefinementMap e o a (ι.trans (Equiv.swap (ι a) b₀).toEmbedding)
    U T _).appTop v.val - (subframeRefinementMap e o a ι U T _).appTop v.val = 0
  rw [hselect, hselect, sub_self]

/-- Exact image lifts have zero original localized class when a full source lift is available. -/
theorem originalLocalizedExchangeClass_relation_image_zero
    (u : Sinv) (hu : α u = tS) (he : u.val ∈ CS)
    (b₀ : Fin n) (M : Submonoid Ω) (v : Tinv) (hv : β v = tT) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a T hT hTW hSel ι b₀ M v = 0 := by
  obtain ⟨w, hw, hwx⟩ := originalRelationSubframeImage_exchange_lift
    f hL d V c k n o W U hU hUW m' a ι t u hu he b₀
  rw [originalLocalizedExchangeClass_zero_iff_lift]
  refine ⟨1, w, ?_, hwx⟩
  simpa only [OneMemClass.coe_one, map_one, one_mul, hv] using hw

end FLT.Mazur.HilbertChart.AffineRestriction

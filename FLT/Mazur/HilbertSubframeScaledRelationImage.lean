/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryFaithfulDifferences
public import FLT.Mazur.HilbertSubframeCoverBoundary
public import FLT.Mazur.HilbertSubframeLocalizedEmbeddingLifts
public import FLT.Mazur.EquivalenceRelationSubframeRelationLifts

/-!
# Descending scaled full-relation source numerators

A source numerator with an original scalar factor descends to the strict
image with the same exact boundary factor. Faithful boundary pullback keeps
the original scalar unchanged; no unscaled global source lift is required.
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

local notation "σS" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σT" => normalizedOriginalScalarMap f hL d V c k m' a W T hT hTW
attribute [local irreducible] normalizedOriginalScalarMap

/-- Faithful boundary descent carries the original scalar factor to the strict image. -/
theorem originalRelationSubframeImage_scaled_lifts (x : Ω) (u : Sinv)
    (hu : α u = α (σS x) * tS) (he : u.val ∈ CS)
    (v₀ : Tinv) (hv₀ : β v₀ = tT) :
    ∃ v : Tinv, β v = β (σT x) * tT ∧
      ∀ κ : Fin m' ↪ Fin n,
        (subframeRefinementMap e o a κ U T (hSel κ)).appTop v.val = u.val := by
  obtain ⟨v, hv, _⟩ := subframe_sourceRelation_existsUnique e o a U hU ι ⟨u.val, he⟩
  let _ : Surjective (subframeRefinementMap e o a ι U T (hSel ι)) :=
    subframeImageCover_surjective e o a U ι
  have hboundary : β v = β (σT x * v₀) := by
    apply Subtype.ext
    apply (InvariantBoundary.subframeBoundaryRefinement_eq_iff
      e o a ι i z r s hr hs U T (hSel ι) v.val (σT x * v₀).val).mpr
    change (subframeRefinementMap e o a ι U T (hSel ι)).appTop v.val = u.val at hv
    rw [hv]
    exact (congrArg Subtype.val hu).trans
      (normalizedScaledBoundaryLift_subframe f hL d V c k n o W U hU hUW
        m' a T hT hTW hSel ι t x v₀ (σT x * v₀) hv₀ (map_mul β _ _)).symm
  refine ⟨v, ?_, subframeImageCover_descended_all e o a U hU ι u v hv⟩
  simpa only [map_mul, hv₀] using hboundary

/-- A scaled full source numerator supplies a zero-exchange target numerator. -/
theorem originalRelationSubframeImage_scaled_exchange_lift (x : Ω) (u : Sinv)
    (hu : α u = α (σS x) * tS) (he : u.val ∈ CS)
    (v₀ : Tinv) (hv₀ : β v₀ = tT) (b₀ : Fin n) :
    ∃ v : Tinv, β v = β (σT x) * tT ∧
      subframeExchangeMap e o a U T hT hSel ι b₀ v = 0 := by
  obtain ⟨v, hv, hselect⟩ := originalRelationSubframeImage_scaled_lifts
    f hL d V c k n o W U hU hUW m' a ι t x u hu he v₀ hv₀
  refine ⟨v, hv, ?_⟩
  change (subframeRefinementMap e o a (ι.trans (Equiv.swap (ι a) b₀).toEmbedding)
    U T _).appTop v.val - (subframeRefinementMap e o a ι U T _).appTop v.val = 0
  rw [hselect, hselect, sub_self]

/-- Inverting the original numerator scalar kills the original localized exchange class. -/
theorem originalLocalizedExchangeClass_scaled_relation_image_zero
    (M : Submonoid Ω) (x : M) (u : Sinv)
    (hu : α u = α (σS x.val) * tS) (he : u.val ∈ CS)
    (v₀ : Tinv) (hv₀ : β v₀ = tT) (b₀ : Fin n) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a T hT hTW hSel ι b₀ M v₀ = 0 := by
  obtain ⟨v, hv, hex⟩ := originalRelationSubframeImage_scaled_exchange_lift
    f hL d V c k n o W U hU hUW m' a ι t x.val u hu he v₀ hv₀ b₀
  rw [originalLocalizedExchangeClass_zero_iff_lift]
  exact ⟨x, v, by simpa only [hv₀] using hv, hex⟩

end FLT.Mazur.HilbertChart.AffineRestriction

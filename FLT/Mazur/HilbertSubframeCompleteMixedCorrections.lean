/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMixedResidualBranches
public import FLT.Mazur.HilbertSubframeCompleteImageLifts
public import FLT.Mazur.EquivalenceRelationCompleteSubframeCompatibility

/-!
# Full original mixed corrections on complete subframe image charts

The geometrically descended source and target lifts solve the whole mixed
relation, including its residual part. Subtracting them from independent exact
lifts constructs actual boundary-kernel corrections with the prescribed full
mixed error. The entire source chart must still be complete.
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

open EquivalenceRelationNormalizedFrames.MixedFrames
local notation "F" => mixedChartFirst o a U T
local notation "G" => mixedChartSecond o a U T

include ha hc in
/-- Exact original boundary lifts can be chosen compatible on the whole mixed relation. -/
theorem originalCompleteSubframeImage_full_lifts :
    ∃ (u : Sinv) (v : Tinv), α u = tS ∧ β v = tT ∧
      (F).appTop u.val = (G).appTop v.val := by
  obtain ⟨u, v, hu, hv, huv⟩ := originalCompleteSubframeImage_lifts
    f hL d V c k n o W U hU hUW m' a ι t ha hc
  let _ := normalizedFrameSource_separated f hL d V c k m' a
  exact ⟨u, v, hu, hv, completeSubframeLift_mixed e o a U T hU hSel hc ι u v.val huv⟩

include ha hc in
/-- Independent exact lifts have actual boundary-zero corrections for their full mixed error. -/
theorem originalCompleteSubframeImage_full_corrections (u₀ : Sinv) (v₀ : Tinv)
    (hu₀ : α u₀ = tS) (hv₀ : β v₀ = tT) :
    ∃ (du : Sinv) (dv : Tinv), α du = 0 ∧ β dv = 0 ∧
      (F).appTop du.val - (G).appTop dv.val =
        (F).appTop u₀.val - (G).appTop v₀.val := by
  obtain ⟨u, v, hu, hv, he⟩ := originalCompleteSubframeImage_full_lifts
    f hL d V c k n o W U hU hUW m' a ι t ha hc
  refine ⟨u₀ - u, v₀ - v, ?_, ?_, ?_⟩
  · rw [map_sub, hu₀, hu, sub_self]
  · rw [map_sub, hv₀, hv, sub_self]
  · change (F).appTop (u₀.val - u.val) - (G).appTop (v₀.val - v.val) = _
    rw [map_sub, map_sub, he]
    abel

end FLT.Mazur.HilbertChart.AffineRestriction

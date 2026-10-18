/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceCompactRelation
public import FLT.Mazur.HilbertSubframeScaledRelationImage

/-!
# Original-prime image exchange vanishing from compatible open lifts

The actual quasicompact full relation extends an open lift to a source
numerator. Faithful image descent retains its original denominator. Inverting
that denominator kills the original image exchange class at the same original
boundary source prime, including residual equations and nilpotents.
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

local notation "τU" => restrictedAction τ U hU
local notation "jU" => j ∣_ U
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
local notation "σ₀" => invariantScalarCoordinates τU σS
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)
attribute [local irreducible] SchemeRelationRestriction.doubleDomain
  SchemeRelationRestriction.fst SchemeRelationRestriction.snd
variable (ha : IsAffineOpen U) (O : U.toScheme.Opens)
  (hO : ∀ g : Equiv.Perm (Fin n),
    (restrictedAction (normalizedFullRelationAction f hL d V c k n o) U hU g).hom ⁻¹ᵁ O = O)

include ha in
/-- Open source solvability kills strict-image exchanges at the unchanged original prime. -/
theorem originalLocalizedExchangeClass_pairOpen_source_zero
    (P : Ideal Tsource) [P.IsPrime]
    (hP : PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈
      SchemeScalarPrincipalNeighborhood.scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction τU O hO))
    (hb : ((jU) ∣_ O).appTop v.val = ((jU) ⁻¹ᵁ O).ι.appTop (tS).val)
    (he : (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val)
    (v₀ : Tinv) (hv₀ : β v₀ = tT) (b₀ : Fin n) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a T hT hTW hSel ι b₀
        (originalSubframePrimeDenominators f hL d V c k W P) v₀ = 0 := by
  obtain ⟨x₀, hx, u, hu, hrel⟩ := originalSource_pairOpen_lift
    f hL d V c k n o W U hU hUW ha O hO P hP v (tS).val hb he
  apply originalLocalizedExchangeClass_scaled_relation_image_zero
    f hL d V c k n o W U hU hUW m' a ι t
    (originalSubframePrimeDenominators f hL d V c k W P) ⟨x₀, hx⟩ u
    _ hrel v₀ hv₀ b₀
  exact Subtype.ext hu

end FLT.Mazur.HilbertChart.AffineRestriction

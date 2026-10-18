/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertEqualFrameBoundaryCorrections
public import FLT.Mazur.HilbertNormalizedBoundarySurjectivity
public import FLT.Mazur.HilbertMixedResidualBranches
public import FLT.Mazur.EquivalenceRelationMixedResidualExtension

/-!
# Constructed original-boundary lifts with only residual discrepancies

Restrict one invariant lift from a common stable affine normalized chart.
Every subchart retains the exact original boundary value, and every pairwise
discrepancy is the extension of its actual residual coefficient. No choice of
separate chart lifts, completeness, or vanishing on the residual is assumed.
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

local instance equalFrameResidual_sourceSeparated :
    (source p q (Fin n) o).IsSeparated := normalizedFrameSource_separated f hL d V c k n o

include hU in
/-- Common affine geometry constructs lifts whose full errors are exactly residual-supported. -/
theorem exists_originalEqualFrame_residual_lifts (ha : IsAffineOpen U)
    {T : Type} (Us : T → (normalizedFullRelationFrames f hL d V c k n o).Opens)
    (hUs : ∀ a σ, (τ σ).hom ⁻¹ᵁ Us a = Us a) (h : ∀ a, Us a ≤ U) :
    ∃ v : ∀ a, invariantCoordinates (restrictedAction τ (Us a) (hUs a)),
      (∀ a, normalizedBoundaryChartMap f hL d V c k n o (Us a) (hUs a) (v a) =
        normalizedOrbitBoundaryCoefficient f hL d V c k n o W (Us a) (hUs a)
          ((h a).trans hUW) t) ∧
      ∀ a b,
        let M := MixedFrames.mixedChartOpen o o (Us a) (Us b)
        let x := (MixedFrames.mixedChartFirst o o (Us a) (Us b)).appTop (v a).val -
          (MixedFrames.mixedChartSecond o o (Us a) (Us b)).appTop (v b).val
        x = MixedFrames.mixedResidualSectionExtension e o o M.ι
          ((MixedFrames.mixedResidualTestOpen e o o M.ι).ι.appTop x) := by
  obtain ⟨w, hw⟩ := normalizedBoundaryChartMap_surjective f hL d V c k n o U hU ha
    (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
  let v a := FiniteGroupOpenRelation.invariantRestriction τ U hU (Us a) (hUs a) (h a) w
  refine ⟨v, fun a ↦ ?_, fun a b ↦ ?_⟩
  · exact normalizedOrbitBoundaryLift_refinement f hL d V c k n o W U hU hUW
      (Us a) (hUs a) (h a) t w hw
  · apply (MixedFrames.mixedResidualSectionExtension_reconstruct e o o _ _ ?_).symm
    intro ι
    rw [map_sub, sub_eq_zero]
    exact MixedFrames.mixedEqualFrame_restrictions_equalize e (Fin n) o U hU
      (Us a) (Us b) (hUs a) (hUs b) (h a) (h b) w ι

end FLT.Mazur.HilbertChart.AffineRestriction

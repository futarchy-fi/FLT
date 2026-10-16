/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCoefficients
public import FLT.Mazur.EquivalenceRelationChartFamilyLifts
public import FLT.Mazur.HilbertJointOrbitBoundaryLifts

/-!
# Simultaneous Hilbert chart lifts of an original orbit-domain boundary section

All chart lifts are chosen once. Their differences lie in the exact boundary
ideals of the entire original mixed relations. A single correction obstruction
records whether all ambient equations can be solved simultaneously.
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
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  EquivalenceRelationNormalizedFrames.InvariantBoundary.boundary
open MixedFrames.ChartFamily
variable {ι : Type} (n : ι → ℕ) (o : ∀ a, Fin (n a))
  (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (U : ∀ a, (normalizedFullRelationFrames f hL d V c k (n a) (o a)).Opens)
  (hU : ∀ a σ,
    (normalizedFullRelationAction f hL d V c k (n a) (o a) σ).hom ⁻¹ᵁ U a = U a)
  (hUW : ∀ a, U a ≤ normalizedFullRelationFirst f hL d V c k (n a) (o a) ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
  (hUa : ∀ a, IsAffineOpen (U a))
local notation "hdom" => fun a ↦ normalizedOrbitBoundary_domain_le
  f hL d V c k (n a) (o a) W (U a) (hUW a)
local notation "teq" => jointOrbitBoundaryFunction_equalized f hL d V c k W t

/-- One actual invariant lift per affine chart, shared across every comparison with other charts. -/
def orbitBoundaryFamilyLift : MixedFrames.ChartFamily.Sections e n o U hU :=
  MixedFrames.ChartFamily.liftFamily e n o U hU i z r s hr hs Uc (pullOpen_preimage_eq ec Wc) hdom
    (orbitFunctions ec Wc t).val teq hUa

/-- The chosen lifts retain the given original boundary section on its unchanged orbit domain. -/
theorem orbitBoundaryFamilyLift_restrict (a : ι) :
    normalizedBoundaryChartMap f hL d V c k (n a) (o a) (U a) (hU a)
      (orbitBoundaryFamilyLift f hL d V c k n o W U hU hUW t hUa a) =
        normalizedOrbitBoundaryCoefficient f hL d V c k (n a) (o a) W (U a) (hU a)
          (hUW a) t := by
  apply Subtype.ext
  simp only [normalizedBoundaryChartMap, invariantMap_val,
    normalizedOrbitBoundaryCoefficient_val]
  exact congrFun (MixedFrames.ChartFamily.liftFamily_restriction e n o U hU i z r s hr hs Uc
    (pullOpen_preimage_eq ec Wc) hdom (orbitFunctions ec Wc t).val teq hUa) a

/-- The family discrepancy is in the full original mixed boundary ideal, retaining nilpotents. -/
theorem orbitBoundaryFamilyLift_difference (a b : ι) :
    MixedFrames.ChartFamily.difference e n o U hU
      (orbitBoundaryFamilyLift f hL d V c k n o W U hU hUW t hUa) a b ∈
      RingHom.ker (MixedFrames.mixedChartBoundaryInclusion
        (o a) (o b) (U a) (U b) i).appTop.hom :=
  MixedFrames.ChartFamily.liftFamily_difference_mem_kernel e n o U hU i z r s hr hs Uc
    (pullOpen_preimage_eq ec Wc) hdom (orbitFunctions ec Wc t).val teq hUa a b

/-- The actual original section's simultaneous correction obstruction across all selected charts. -/
def orbitBoundaryFamilyObstruction :=
  MixedFrames.ChartFamily.defect e n o U hU i
    (orbitBoundaryFamilyLift f hL d V c k n o W U hU hUW t hUa)

/-- Vanishing gives one corrected invariant family satisfying every full mixed relation equation. -/
theorem orbitBoundaryFamilyObstruction_eq_zero_iff :
    orbitBoundaryFamilyObstruction f hL d V c k n o W U hU hUW t hUa = 0 ↔
      ∃ v : MixedFrames.ChartFamily.Sections e n o U hU,
        MixedFrames.ChartFamily.restriction e n o U hU i v =
          MixedFrames.ChartFamily.boundaryCoefficient n o U i Uc hdom (orbitFunctions ec Wc t).val ∧
        ∀ a b, (MixedFrames.mixedChartFirst (o a) (o b) (U a) (U b)).appTop (v a).val =
          (MixedFrames.mixedChartSecond (o a) (o b) (U a) (U b)).appTop (v b).val :=
  MixedFrames.ChartFamily.originalObstruction_eq_zero_iff e n o U hU i z r s hr hs Uc
    (pullOpen_preimage_eq ec Wc) hdom (orbitFunctions ec Wc t).val teq hUa

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryFiniteAtlas
public import FLT.Mazur.HilbertOrbitBoundaryFamilyLifts

/-!
# Simultaneous boundary lifts on the finite original-source atlas

Affineness has selected a finite family that covers the whole source. Choose
one actual invariant boundary lift per selected chart. The remaining correction
equations use finitely many pairs of full mixed relations.
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
namespace OrbitBoundaryAtlas.FiniteAtlas
set_option quotPrecheck false
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "C" => finiteCharts f hL d V c k W hW
local notation "n" => fun a : C ↦ a.val.size
local notation "o" => fun a : C ↦ a.val.label
local notation "U" => fun a : C ↦ a.val.domain
local notation "hU" => fun a : C ↦ a.val.stable
local notation "hUW" => fun a : C ↦ a.val.overDomain
local notation "ha" => fun a : C ↦ a.val.affine
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Invariant ambient sections on the finitely many selected charts. -/
abbrev Sections := MixedFrames.ChartFamily.Sections e n o U hU

/-- One chosen invariant lift on every chart of the finite source cover. -/
def lifts : Sections f hL d V c k W hW :=
  orbitBoundaryFamilyLift f hL d V c k n o W U hU hUW t ha

/-- Every lift restricts to the unchanged original section along its exact closed boundary. -/
theorem lifts_restrict (a : C) :
    normalizedBoundaryChartMap f hL d V c k a.val.size a.val.label a.val.domain a.val.stable
      (lifts f hL d V c k W hW t a) =
        normalizedOrbitBoundaryCoefficient f hL d V c k a.val.size a.val.label W a.val.domain
          a.val.stable
          a.val.overDomain t :=
  orbitBoundaryFamilyLift_restrict f hL d V c k n o W U hU hUW t ha a

/-- All discrepancies lie in the original mixed boundary ideals, retaining nilpotents. -/
theorem lifts_difference (a b : C) :
    MixedFrames.ChartFamily.difference e n o U hU (lifts f hL d V c k W hW t) a b ∈
      RingHom.ker (MixedFrames.mixedChartBoundaryInclusion
        a.val.label b.val.label a.val.domain b.val.domain i).appTop.hom :=
  orbitBoundaryFamilyLift_difference f hL d V c k n o W U hU hUW t ha a b

/-- The actual obstruction on a proved finite source atlas. -/
def obstruction := orbitBoundaryFamilyObstruction f hL d V c k n o W U hU hUW t ha

/-- Vanishing constructs compatible invariant lifts on every member of the finite atlas. -/
theorem obstruction_eq_zero_iff :
    obstruction f hL d V c k W hW t = 0 ↔ ∃ v : Sections f hL d V c k W hW,
      (∀ a : C, normalizedBoundaryChartMap f hL d V c k a.val.size a.val.label a.val.domain
        a.val.stable
        (v a) = normalizedOrbitBoundaryCoefficient f hL d V c k a.val.size a.val.label W
          a.val.domain a.val.stable a.val.overDomain t) ∧
      ∀ a b : C, (MixedFrames.mixedChartFirst a.val.label b.val.label a.val.domain
        b.val.domain).appTop
        (v a).val = (MixedFrames.mixedChartSecond a.val.label b.val.label a.val.domain
          b.val.domain).appTop
          (v b).val := by
  change MixedFrames.ChartFamily.defect e n o U hU i (lifts f hL d V c k W hW t) = 0 ↔ _
  rw [MixedFrames.ChartFamily.defect_eq_zero_iff_compatible]
  constructor
  · rintro ⟨v, hv, hc⟩
    refine ⟨v, fun a ↦ ?_, hc⟩
    apply Subtype.ext
    exact (congrFun hv a).trans
      (congrArg Subtype.val (lifts_restrict f hL d V c k W hW t a))
  · rintro ⟨v, hv, hc⟩
    refine ⟨v, funext fun a ↦ ?_, hc⟩
    exact congrArg Subtype.val ((hv a).trans (lifts_restrict f hL d V c k W hW t a).symm)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction

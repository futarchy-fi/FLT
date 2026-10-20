/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryCorrectionIdeal
public import FLT.Mazur.InvariantOpenRelationSectionScalars

/-!
# The old Hilbert chart scalars in full original equalizer coordinates

The original invariant chart rings are retained. Their scalar maps factor
through the equalizer of the entire relation on the unchanged orbit open,
and their inclusions are the actual scheme pullbacks constructed for sections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
  scalarFamily normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "Charts" => finiteCharts f hL d V c k W hW

open BaseLocalizationMap
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "F" => MixedFrames.ChartFamily.firstCoefficientMap ef n o U hU
local notation "G" => MixedFrames.ChartFamily.secondCoefficientMap ef n o U hU
local notation "H" => fun j : Charts ↦ normalizedBoundaryChartMap f hL d V c k j.val.size
  j.val.label j.val.domain j.val.stable

local notation "p₀" => (InvariantOpenRelationDiagram.fst (fst f hL d V c k) E).left
local notation "q₀" => (InvariantOpenRelationDiagram.snd (fst f hL d V c k)
  (snd f hL d V c k) E (pullOpen_preimage_eq e W)).left
local notation "Ω₀" => SchemeEffectiveEpiSections.compatibleFunctions p₀ q₀
local notation "eqv" => orbitCompatibleFunctions e W

/-- The unchanged invariant chart receives scalars from the full original equalizer. -/
def originalChartEqualizerScalarMap (j : Charts) :
    Ω₀ →+* chartCoordinateRing f hL d V c k W hW j :=
  (originalChartScalarMap f hL d V c k W hW j).comp (eqv).symm.toRingHom

/-- Returning to the prescribed invariant sheaf recovers the old scalar map exactly. -/
theorem originalChartEqualizerScalarMap_comp (j : Charts) :
    (originalChartEqualizerScalarMap f hL d V c k W hW j).comp (eqv).toRingHom =
      originalChartScalarMap f hL d V c k W hW j := by
  ext r
  exact congrArg (originalChartScalarMap f hL d V c k W hW j)
    ((eqv).symm_apply_apply r)

/-- Its underlying full section is the literal scalar map of the original chart scheme. -/
theorem originalChartEqualizerScalarMap_val (j : Charts) (r : Ω₀) :
    (originalChartEqualizerScalarMap f hL d V c k W hW j r).val =
      SchemeRelationSectionScalars.scalarMap p₀ q₀ (chartMap f hL d V c k W j.val) ⊤ r := by
  change (scalarFamily f hL d V c k W hW ((eqv).symm r) j).val = _
  rw [scalarFamily_val]
  have hr : (orbitFunctions e W ((eqv).symm r)).val = r.val :=
    congrArg Subtype.val ((eqv).apply_symm_apply r)
  rw [hr]
  change _ = (chartMap f hL d V c k W j.val).appLE ⊤ ⊤ le_top r.val
  exact ConcreteCategory.congr_hom
    (@Scheme.Hom.app_eq_appLE _ _ (chartMap f hL d V c k W j.val) ⊤) r.val

/-- Every full mixed equation uses these same equalizer scalars at both endpoints. -/
theorem originalChartEqualizerScalarMap_mixed (j l : Charts) (r : Ω₀) :
    F j l (originalChartEqualizerScalarMap f hL d V c k W hW j r) =
      G j l (originalChartEqualizerScalarMap f hL d V c k W hW l r) := by
  exact originalChartScalarMap_full_compatible f hL d V c k W hW j l ((eqv).symm r)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction

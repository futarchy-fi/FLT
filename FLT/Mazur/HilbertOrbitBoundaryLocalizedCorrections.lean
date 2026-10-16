/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLocalizedNumerators

/-!
# Constructed kernel corrections from compatible localized chart solutions

Subtract the exact cleared numerators from the scaled chosen chart lifts.
The resulting corrections vanish on the original boundary and enforce all
full mixed compatibility equations after one common power.
-/

public noncomputable section
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

open PrincipalLocalizationMap
local notation "ef" => fullRelationSchemeEquivalence f hL d V c k
local notation "n" => fun j : Charts ↦ j.val.size
local notation "o" => fun j : Charts ↦ j.val.label
local notation "U" => fun j : Charts ↦ j.val.domain
local notation "hU" => fun j : Charts ↦ j.val.stable
local notation "F" => MixedFrames.ChartFamily.firstCoefficientMap ef n o U hU
local notation "G" => MixedFrames.ChartFamily.secondCoefficientMap ef n o U hU
local notation "H" => fun j : Charts ↦ normalizedBoundaryChartMap f hL d V c k j.val.size
  j.val.label j.val.domain j.val.stable

variable (a : (invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))
local notation "r" => scalarFamily f hL d V c k W hW a

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

variable (v : ∀ j : finiteCharts f hL d V c k W hW,
  Localization.Away (scalarFamily f hL d V c k W hW a j))

/-- Localized solutions construct simultaneous invariant kernel corrections after scaling. -/
theorem original_scaled_kernel_corrections_of_localized
    (hb : ∀ j : Charts, localizedChartBoundaryMap f hL d V c k W hW a j (v j) =
      algebraMap _ _ (normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
        j.val.domain j.val.stable j.val.overDomain t))
    (he : ∀ j l : Charts, localizedChartFirstMap f hL d V c k W hW a j l (v j) =
      localizedChartSecondMap f hL d V c k W hW a j l (v l)) :
    ∃ N : ℕ, ∃ correction : Sections f hL d V c k W hW,
      (∀ j : Charts, H j (correction j) = 0) ∧
      (∀ j l : Charts,
        F j l (r j ^ N * lifts f hL d V c k W hW t j - correction j) =
        G j l (r l ^ N * lifts f hL d V c k W hW t l - correction l)) :=
  FiniteLocalizedBoundaryLifts.corrections_of_numerators
    (A := fun j : Charts ↦ invariantCoordinates
      (restrictedAction (action ef (Fin j.val.size) j.val.label)
        j.val.domain j.val.stable))
    (B := chartBoundaryCoordinateRing f hL d V c k W hW)
    (C := mixedCoordinateRing f hL d V c k W hW) H F G r
    (lifts f hL d V c k W hW t)
    (fun j ↦ normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
      j.val.domain j.val.stable j.val.overDomain t)
    (lifts_restrict f hL d V c k W hW t)
    (original_numerators_of_localized f hL d V c k W hW a t v hb he)

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction

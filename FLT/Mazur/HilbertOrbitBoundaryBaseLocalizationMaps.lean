/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryLocalizedMaps
public import FLT.Mazur.BaseLocalizationMap

/-!
# Original scalar maps and arbitrary base localization on the finite Hilbert atlas

Every chart scalar map is a ring homomorphism from the unchanged invariant
section ring. Localize the exact boundary and FULL mixed coefficient maps at
images of any original multiplicative set, including any prime complement.
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

/-- The actual chart coefficient of an original scalar, as a ring homomorphism. -/
def originalChartScalarMap (j : Charts) :
    (invariantSheaf e).obj.obj (op W) →+* chartCoordinateRing f hL d V c k W hW j where
  toFun a := scalarFamily f hL d V c k W hW a j
  map_zero' := by
    apply Subtype.ext
    simp only [scalarFamily_val, map_zero, ZeroMemClass.coe_zero]
  map_one' := by
    apply Subtype.ext
    simp only [scalarFamily_val, map_one, OneMemClass.coe_one]
  map_add' a b := by
    apply Subtype.ext
    simp only [scalarFamily_val, map_add, Subalgebra.coe_add, Subring.coe_add]
  map_mul' a b := by
    apply Subtype.ext
    simp only [scalarFamily_val, map_mul, Subalgebra.coe_mul, Subring.coe_mul]

/-- This ring homomorphism uses exactly the previously constructed scalar family. -/
theorem originalChartScalarMap_apply (a : (invariantSheaf e).obj.obj (op W)) (j : Charts) :
    originalChartScalarMap f hL d V c k W hW j a = scalarFamily f hL d V c k W hW a j := rfl

variable (M : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))
local notation "α" => originalChartScalarMap f hL d V c k W hW

/-- Localized chart coefficients with denominators from the original multiplicative set. -/
abbrev baseLocalizedChartRing (j : Charts) := Localization (M.map (α j).toMonoidHom)

/-- Localization of the exact original chart boundary. -/
abbrev baseLocalizedBoundaryRing (j : Charts) :=
  Localization (M.map ((H j).comp (α j)).toMonoidHom)

/-- Localization of the full mixed relation, retaining independent chart labels and sizes. -/
abbrev baseLocalizedMixedRing (j l : Charts) :=
  Localization (M.map ((F j l).comp (α j)).toMonoidHom)

/-- The exact original boundary map localized at the original scalar multiplicative set. -/
def baseLocalizedBoundaryMap (j : Charts) :
    baseLocalizedChartRing f hL d V c k W hW M j →+*
      baseLocalizedBoundaryRing f hL d V c k W hW M j :=
  BaseLocalizationMap.map M (α j) ((H j).comp (α j)) (H j) (fun _ ↦ rfl)

/-- The first full mixed pullback at original base denominators. -/
def baseLocalizedFirstMap (j l : Charts) :
    baseLocalizedChartRing f hL d V c k W hW M j →+*
      baseLocalizedMixedRing f hL d V c k W hW M j l :=
  BaseLocalizationMap.map M (α j) ((F j l).comp (α j)) (F j l) (fun _ ↦ rfl)

/-- The second full mixed pullback uses the proved compatibility of all original scalars. -/
def baseLocalizedSecondMap (j l : Charts) :
    baseLocalizedChartRing f hL d V c k W hW M l →+*
      baseLocalizedMixedRing f hL d V c k W hW M j l :=
  BaseLocalizationMap.map M (α l) ((F j l).comp (α j)) (G j l)
    (fun a ↦ (scalarFamily_compatible f hL d V c k W hW a j l).symm)

/-- The localized exact boundary map retains original coefficients. -/
theorem baseLocalizedBoundaryMap_algebraMap (j : Charts)
    (a : chartCoordinateRing f hL d V c k W hW j) :
    baseLocalizedBoundaryMap f hL d V c k W hW M j (algebraMap _ _ a) =
      algebraMap _ _ (H j a) := BaseLocalizationMap.map_algebraMap _ _ _ _ _ a

/-- The localized first full mixed map retains original coefficients. -/
theorem baseLocalizedFirstMap_algebraMap (j l : Charts)
    (a : chartCoordinateRing f hL d V c k W hW j) :
    baseLocalizedFirstMap f hL d V c k W hW M j l (algebraMap _ _ a) =
      algebraMap _ _ (F j l a) := BaseLocalizationMap.map_algebraMap _ _ _ _ _ a

/-- The localized second full mixed map retains original coefficients. -/
theorem baseLocalizedSecondMap_algebraMap (j l : Charts)
    (a : chartCoordinateRing f hL d V c k W hW l) :
    baseLocalizedSecondMap f hL d V c k W hW M j l (algebraMap _ _ a) =
      algebraMap _ _ (G j l a) := BaseLocalizationMap.map_algebraMap _ _ _ _ _ a

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction

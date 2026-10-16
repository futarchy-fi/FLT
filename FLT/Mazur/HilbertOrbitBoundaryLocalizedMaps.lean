/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryScaledMultipliers
public import FLT.Mazur.EquivalenceRelationChartFamilyLocalization

/-!
# Localized finite chart rings and their original coefficient maps

Use the canonical compatible chart family of a specified original scalar.
Localized boundary lifts satisfying all localized full mixed equations give
an actual power of that scalar in the original lifting ideal. Neither exact
unlocalized chart compatibility nor kernel corrections are assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.FiniteLocalizedBoundaryLifts
/-- Exact scaled numerators construct simultaneous kernel corrections to chosen boundary lifts. -/
theorem corrections_of_numerators {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
    (φ : ∀ i, A i →+* B i) (p : ∀ i j, A i →+* C i j) (q : ∀ i j, A j →+* C i j)
    (r s : ∀ i, A i) (t : ∀ i, B i) (hs : ∀ i, φ i (s i) = t i)
    (h : ∃ N : ℕ, ∃ w : ∀ i, A i,
      (∀ i, φ i (w i) = φ i (r i) ^ N * t i) ∧
      (∀ i j, p i j (w i) = q i j (w j))) :
    ∃ N : ℕ, ∃ z : ∀ i, A i,
      (∀ i, φ i (z i) = 0) ∧
      (∀ i j, p i j (r i ^ N * s i - z i) = q i j (r j ^ N * s j - z j)) := by
  obtain ⟨N, w, hw, hc⟩ := h
  refine ⟨N, fun i ↦ r i ^ N * s i - w i, ?_, ?_⟩
  · intro i
    rw [map_sub, map_mul, map_pow, hs i, hw i, sub_self]
  · intro i j
    simpa only [sub_sub_cancel] using hc i j
end FLT.Mazur.FiniteLocalizedBoundaryLifts

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

/-- The actual invariant coefficient ring of a selected ambient chart. -/
abbrev chartCoordinateRing (j : Charts) := invariantCoordinates
  (restrictedAction (normalizedFullRelationAction f hL d V c k j.val.size j.val.label)
    j.val.domain j.val.stable)

/-- The actual invariant coefficient ring of the exact selected chart boundary. -/
abbrev chartBoundaryCoordinateRing (j : Charts) := invariantCoordinates
  (boundaryOpenAction
    (normalizedOriginalBoundaryAction f hL d V c k j.val.size j.val.label)
    (normalizedFullRelationAction f hL d V c k j.val.size j.val.label)
    (normalizedOriginalBoundaryInclusion f hL d V c k j.val.size j.val.label)
    (normalizedOriginalBoundaryAction_inclusion f hL d V c k j.val.size j.val.label)
    j.val.domain j.val.stable)

/-- The original full mixed relation coefficient ring for two independently selected charts. -/
abbrev mixedCoordinateRing (j l : Charts) : Type :=
  Γ((MixedFrames.mixedChartOpen j.val.label l.val.label j.val.domain l.val.domain).toScheme, ⊤)

variable (a : (invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))
local notation "r" => scalarFamily f hL d V c k W hW a

/-- Actual localization of the invariant boundary map at the original scalar coefficient. -/
def localizedChartBoundaryMap (j : Charts) :
    Localization.Away (r j) →+* Localization.Away (H j (r j)) :=
  map (H j) (r j) (H j (r j)) rfl

/-- First localized pullback to the full mixed relation ring. -/
def localizedChartFirstMap (j l : Charts) :
    Localization.Away (r j) →+* Localization.Away (F j l (r j)) :=
  map (F j l) (r j) (F j l (r j)) rfl

/-- The second localized pullback uses the proved equality of the original scalar coefficients. -/
def localizedChartSecondMap (j l : Charts) :
    Localization.Away (r l) →+* Localization.Away (F j l (r j)) :=
  map (G j l) (r l) (F j l (r j))
    (scalarFamily_compatible f hL d V c k W hW a j l).symm

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

variable (v : ∀ j : finiteCharts f hL d V c k W hW,
  Localization.Away (scalarFamily f hL d V c k W hW a j))


end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction

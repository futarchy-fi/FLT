/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeScalars
public import FLT.Mazur.HilbertOrbitBoundaryBaseLocalizationMaps

/-!
# Original scalar maps on arbitrary Hilbert subframe charts

The original invariant section ring acts on every stable chart over its orbit
open, including independently constructed strict targets. Selected pullbacks
preserve this action. On finite atlas charts this is the existing scalar map.
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

/-- Original invariant scalars pulled back to any stable Hilbert chart. -/
def normalizedOriginalScalarMap : Ω →+* Sinv where
  toFun x := openChartScalar e E (pullOpen_preimage_eq eo W) (orbitFunctions eo W x).val
    (OrbitBoundaryAtlas.FiniteAtlas.original_scalar_equalized f hL d V c k W x)
    o U hU hUW
  map_zero' := by
    apply Subtype.ext
    simp only [openChartScalar_val, map_zero, ZeroMemClass.coe_zero]
  map_one' := by
    apply Subtype.ext
    simp only [openChartScalar_val, map_one, OneMemClass.coe_one]
  map_add' x y := by
    apply Subtype.ext
    simp only [openChartScalar_val, map_add, Subalgebra.coe_add, Subring.coe_add]
  map_mul' x y := by
    apply Subtype.ext
    simp only [openChartScalar_val, map_mul, Subalgebra.coe_mul, Subring.coe_mul]

omit [Etale V.hom] in
/-- The scalar on the full source ring is the unchanged geometric pullback. -/
theorem normalizedOriginalScalarMap_val (x : Ω) :
    (normalizedOriginalScalarMap f hL d V c k n o W U hU hUW x).val =
      ((normalizedFullRelationFirst f hL d V c k n o).resLE E U hUW).appTop
        (orbitFunctions eo W x).val := rfl

attribute [local irreducible] normalizedOriginalScalarMap

variable (m' : ℕ) (a : Fin m')
  (U' : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin m'),
    (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ U' = U')
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

omit [Etale V.hom] in
/-- All selections preserve the original scalar action on independent Hilbert charts. -/
theorem normalizedOriginalScalarMap_subframe (ι : Fin m' ↪ Fin n)
    (h : U ≤ subframeMap e o a ι ⁻¹ᵁ U') (x : Ω) :
    (subframeRefinementMap e o a ι U U' h).appTop
      (normalizedOriginalScalarMap f hL d V c k m' a W U' hU' hU'W x).val =
        (normalizedOriginalScalarMap f hL d V c k n o W U hU hUW x).val := by
  rw [normalizedOriginalScalarMap_val, normalizedOriginalScalarMap_val]
  exact openChartScalar_subframe e E (pullOpen_preimage_eq eo W) (orbitFunctions eo W x).val
    (OrbitBoundaryAtlas.FiniteAtlas.original_scalar_equalized f hL d V c k W x)
    o a U hU hUW U' hU' hU'W ι h

namespace OrbitBoundaryAtlas.FiniteAtlas
/-- This arbitrary-chart scalar map specializes to the existing finite-atlas scalar map. -/
theorem normalizedOriginalScalarMap_finite
    (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
    (idx : finiteCharts f hL d V c k W hW) :
    normalizedOriginalScalarMap f hL d V c k idx.val.size idx.val.label W
      idx.val.domain idx.val.stable idx.val.overDomain =
        originalChartScalarMap f hL d V c k W hW idx := by
  unfold normalizedOriginalScalarMap originalChartScalarMap scalarFamily
  rfl
end OrbitBoundaryAtlas.FiniteAtlas

end FLT.Mazur.HilbertChart.AffineRestriction

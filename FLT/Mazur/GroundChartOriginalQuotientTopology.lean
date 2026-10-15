/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroundChartRelationDiagonal
public import FLT.Mazur.AffineHilbertRestrictedQuotient
public import FLT.Mazur.VariableHilbertGroundQuotientOpen

/-!
# Separating the full original quotient from its changed-ground cover

The changed-family quotient surjects onto the quotient by the full original
relation on the same source. For etale parameter maps the latter embeds
openly into the original orbit space. The factorization preserves the whole
locally ringed morphism. Scheme effectivity of the middle quotient remains open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd invariantLocallyRingedProjection
  variableChartFixedBaseQuotientMap restrictedInvariantQuotientMap
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => pullback.snd f a
local instance groundOriginalTopologySmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
variable {B : Over (Spec (.of S))} (l : B ⟶ variableHilbertTest (pullback.snd f a) d W)


local notation "k" => groundOriginalChart f a hL d V W t l
local notation "E" => variableChartEquivalenceRelation f hL d V c
local notation "D" => equivalence f hL d V c k
local notation "D'" => equivalence q h d W c' l
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l
local notation "r" => groundRelationInclusion f a hL d V W t c l

/-- Quotient further by all original arrows, allowing independent new-ground coordinates. -/
def groundOriginalQuotientMap :
    invariantLocallyRingedSpace D' ⟶ invariantLocallyRingedSpace D :=
  invariantMap D D' (𝟙 B.left) (r).left
    (by simpa only [Over.comp_left, Over.map_map_left, Category.comp_id] using
      congrArg Over.Hom.left (groundRelationInclusion_fst f a hL d V W t c l))
    (by simpa only [Over.comp_left, Over.map_map_left, Category.comp_id] using
      congrArg Over.Hom.left (groundRelationInclusion_snd f a hL d V W t c l))

local notation "M" => groundOriginalQuotientMap f a hL d V W t c l

/-- The further quotient retains every original point of the new source. -/
theorem groundOriginalQuotientMap_apply (x : B.left) :
    (M).base (projection D' x) = projection D x :=
  invariantMap_projection_apply _ _ _ _ _ _ x

/-- The changed-family quotient covers the full original quotient on its source. -/
theorem groundOriginalQuotientMap_surjective : Function.Surjective (M).base := by
  intro z
  obtain ⟨x, rfl⟩ := projection_surjective D z
  exact ⟨projection D' x, groundOriginalQuotientMap_apply f a hL d V W t c l x⟩

/-- The factorization retains the whole original quotient comparison, including its sheaf map. -/
theorem groundOriginalQuotientMap_factorization :
    M ≫ restrictedInvariantQuotientMap f hL d V c k =
      restrictedInvariantQuotientMap q h d W c' l ≫
        variableChartFixedBaseQuotientMap f a hL d V W t c := by
  apply invariantMap_hom_ext D'
  rw [← Category.assoc, groundOriginalQuotientMap, invariantMap_projection,
    Category.assoc, restrictedInvariantQuotientMap_projection,
    restrictedInvariantQuotientMap_projection_assoc,
    variableChartFixedBaseQuotientMap_projection, ← Scheme.Hom.comp_toLRSHom_assoc]
  rw [Category.id_comp]
  change Scheme.Hom.toLRSHom
    (l.left ≫ (variableHilbertFixedBaseProjection f a hL d V W t).left) ≫ _ = _
  rw [Scheme.Hom.comp_toLRSHom_assoc]

/-- Etale translation refinement and an open new chart give an etale original parameter map. -/
instance groundOriginalChart_etale [Etale t.left] [IsOpenImmersion l.left] :
    Etale (k).left := by
  let _ : Etale (variableHilbertFixedBaseProjection f a hL d V W t).left :=
    variableHilbertGroundBase_property f a hL d V W t (@Etale) inferInstance
  change Etale (l.left ≫ (variableHilbertFixedBaseProjection f a hL d V W t).left)
  infer_instance

/-- With the full original relation restored, the orbit comparison is an open embedding. -/
theorem groundOriginalQuotient_isOpenEmbedding
    [Etale V.hom] [Etale t.left] [IsOpenImmersion l.left] :
    IsOpenEmbedding (restrictedInvariantQuotientMap f hL d V c k).base := by
  have he : ⇑(restrictedInvariantQuotientMap f hL d V c k).base =
      restrictedOrbitMap f hL d V c k :=
    funext (restrictedInvariantQuotientMap_apply f hL d V c k)
  rw [he]
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (restrictedOrbitMap_continuous f hL d V c k) (restrictedOrbitMap_injective f hL d V c k)
  apply IsOpenMap.of_comp (projection_continuous D) (projection_surjective D)
  exact (projection_isOpenMap E (variableChartRelationSnd f hL d V c).left.isOpenMap).comp
    (k).left.isOpenMap

/-- Forgetting the extra ground identifications is an open quotient map of orbit spaces. -/
theorem groundOriginalQuotientMap_isOpenQuotientMap
    [Etale V.hom] [Etale W.hom] [Etale t.left] [IsOpenImmersion l.left] :
    IsOpenQuotientMap (M).base := by
  refine ⟨groundOriginalQuotientMap_surjective f a hL d V W t c l,
    (M).base.hom.continuous, ?_⟩
  apply (groundOriginalQuotient_isOpenEmbedding f a hL d V W t c l).isOpenMap_iff.mpr
  change IsOpenMap (M ≫ restrictedInvariantQuotientMap f hL d V c k).base
  rw [groundOriginalQuotientMap_factorization, LocallyRingedSpace.comp_base]
  exact (variableChartFixedBaseQuotientMap_isOpenMap f a hL d V W t c).comp
    (restrictedInvariantQuotientMap_base_isOpenEmbedding q h d W c' l).isOpenMap

end FLT.Mazur.HilbertChart.AffineRestriction

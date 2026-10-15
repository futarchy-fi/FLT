/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRestrictedSectionFunctions
public import FLT.Mazur.AffineHilbertRestrictedOrbits
public import FLT.Mazur.RelativeRelationEtaleSourceFunctions

/-!
# The full original invariant sheaf on etale source images

Effective descent identifies sections on each original orbit image with sections
of the actual restricted invariant quotient. The value formula preserves the
original etale source map and composite scheme pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => variableChartRelationFst f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c
local notation "r" => fst f hL d V c k
local notation "s" => snd f hL d V c k

local notation "e" => variableChartEquivalenceRelation f hL d V c
local notation "a" => equivalence f hL d V c k

variable [Etale V.hom] [Etale k.left]

/-- An etale source embeds its full original orbit quotient openly. -/
theorem etaleRestrictedOrbitMap_isOpenEmbedding :
    Topology.IsOpenEmbedding (restrictedOrbitMap f hL d V c k) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (restrictedOrbitMap_continuous f hL d V c k) (restrictedOrbitMap_injective f hL d V c k)
  apply IsOpenMap.of_comp (projection_continuous a) (projection_surjective a)
  exact (projection_isOpenMap e (variableChartRelationSnd f hL d V c).left.isOpenMap).comp
    k.left.isOpenMap

variable (B : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))

instance etaleRestrictedSectionSource_etale :
    Etale (restrictedSectionSource f hL d V c k B) := by
  dsimp only [restrictedSectionSource]
  infer_instance

/-- The exact original orbit image of an open of the full restricted quotient. -/
def etaleRestrictedSectionImageOpen : TopologicalSpace.Opens (Orbit e) :=
  ⟨restrictedOrbitMap f hL d V c k '' B,
    (etaleRestrictedOrbitMap_isOpenEmbedding f hL d V c k).isOpenMap _ B.isOpen⟩

/-- The composite source generates precisely that quotient open. -/
theorem etaleRestrictedSectionSource_image :
    orbitImageOpen e (variableChartRelationSnd f hL d V c).left.isOpenMap
      (etaleSourceImage (restrictedSectionSource f hL d V c k B)) =
        etaleRestrictedSectionImageOpen f hL d V c k B := by
  ext z
  change (∃ x, (∃ t, (restrictedSectionSource f hL d V c k B) t = x) ∧
    projection e x = z) ↔ ∃ w ∈ B, restrictedOrbitMap f hL d V c k w = z
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨projection a t.val, (mem_fullSectionSourceOpen a B t.val).mp t.property, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, rfl⟩ := projection_surjective a w
    exact ⟨k.left x, ⟨⟨x, (mem_fullSectionSourceOpen a B x).mpr hw⟩, rfl⟩, rfl⟩

/-- The entire composite source lies over the original quotient image. -/
theorem etaleRestrictedSectionSource_le :
    ⊤ ≤ (restrictedSectionSource f hL d V c k B) ⁻¹ᵁ
      (pullOpen e (etaleRestrictedSectionImageOpen f hL d V c k B)).val := by
  intro x _
  exact ⟨projection a x.val, (mem_fullSectionSourceOpen a B x.val).mp x.property, rfl⟩

/-- Sections on every original orbit image equal the actual restricted invariant sections. -/
def etaleRestrictedSheafImageEquiv :
    (invariantSheaf e).obj.obj (op (etaleRestrictedSectionImageOpen f hL d V c k B)) ≃+*
      (invariantSheaf a).obj.obj (op B) :=
  (etaleSourceFunctionEquivOn e (variableChartRelationSnd f hL d V c).left.isOpenMap
    (restrictedSectionSource f hL d V c k B) (etaleRestrictedSectionImageOpen f hL d V c k B)
    (etaleRestrictedSectionSource_image f hL d V c k B)).trans
      (restrictedSectionOriginalEquiv f hL d V c k B).symm

/-- The sheaf comparison uses the actual original composite source pullback. -/
theorem etaleRestrictedSheafImageEquiv_val
    (t : (invariantSheaf e).obj.obj (op (etaleRestrictedSectionImageOpen f hL d V c k B))) :
    (fullSectionFunctionEquiv a B (etaleRestrictedSheafImageEquiv f hL d V c k B t)).val =
        (restrictedSectionSource f hL d V c k B).appLE _ ⊤
          (etaleRestrictedSectionSource_le f hL d V c k B)
          ((invariantInclusion e).hom.app
            (op (etaleRestrictedSectionImageOpen f hL d V c k B)) t) := by
  have h := (restrictedSectionOriginalEquiv f hL d V c k B).apply_symm_apply
    (etaleSourceFunctionEquivOn e (variableChartRelationSnd f hL d V c).left.isOpenMap
      (restrictedSectionSource f hL d V c k B) (etaleRestrictedSectionImageOpen f hL d V c k B)
      (etaleRestrictedSectionSource_image f hL d V c k B) t)
  have hv := congrArg Subtype.val h
  rw [restrictedSectionOriginalEquiv_val] at hv
  exact hv.trans (etaleSourceFunctionEquivOn_appLE e
    (variableChartRelationSnd f hL d V c).left.isOpenMap _ _ _ _
      (etaleRestrictedSectionSource_le f hL d V c k B))

/-- The section comparison with an explicitly identified original quotient open. -/
def etaleRestrictedSheafImageEquivOn (O : TopologicalSpace.Opens (Orbit e))
    (he : etaleRestrictedSectionImageOpen f hL d V c k B = O) :
    (invariantSheaf e).obj.obj (op O) ≃+* (invariantSheaf a).obj.obj (op B) := by
  subst O
  exact etaleRestrictedSheafImageEquiv f hL d V c k B

/-- Domain identification preserves the original composite source pullback. -/
theorem etaleRestrictedSheafImageEquivOn_val (O : TopologicalSpace.Opens (Orbit e))
    (he : etaleRestrictedSectionImageOpen f hL d V c k B = O)
    (t : (invariantSheaf e).obj.obj (op O))
    (h : ⊤ ≤ (restrictedSectionSource f hL d V c k B) ⁻¹ᵁ (pullOpen e O).val) :
    (fullSectionFunctionEquiv a B (etaleRestrictedSheafImageEquivOn f hL d V c k B O he t)).val =
      (restrictedSectionSource f hL d V c k B).appLE _ ⊤ h
        ((invariantInclusion e).hom.app (op O) t) := by
  subst O
  exact etaleRestrictedSheafImageEquiv_val f hL d V c k B t

end FLT.Mazur.HilbertChart.AffineRestriction

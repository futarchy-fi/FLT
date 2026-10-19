/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicComparisonGeometry
public import FLT.Mazur.CyclicCharacteristicDisjointComparisonArrows
public import FLT.Mazur.CyclicCharacteristicFiniteTypeAtlas

/-!
# Noetherian geometry of the actual full comparison groupoid

Products of the normalized finite type integer schemes are Noetherian. The
constructed affine comparison maps, including the closed subgroup conditions,
make every ordered-pair relation Noetherian. The finite disjoint union retains
this property, so its actual relation domains are compact.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)

/-- The actual scheme product is the fiber product over the integers. -/
theorem normalizedProduct_isPullback :
    IsPullback (prod.fst : normalizedProduct n b c ⟶ normalizedLocus n b) prod.snd
      (normalizedLocusToInt n b) (normalizedLocusToInt n c) := by
  convert IsPullback.of_is_product'
    (prodIsProd (normalizedLocus n b) (normalizedLocus n c))
    specZIsTerminal using 1 <;> exact specZIsTerminal.hom_ext _ _

/-- Projection from the parameter product is locally of finite type. -/
instance normalizedProduct_fst_locallyOfFiniteType :
    LocallyOfFiniteType (prod.fst : normalizedProduct n b c ⟶ normalizedLocus n b) := by
  rw [← (normalizedProduct_isPullback n b c).isoPullback_hom_fst]
  infer_instance

/-- Projection from the parameter product is quasi-compact. -/
instance normalizedProduct_fst_quasiCompact :
    QuasiCompact (prod.fst : normalizedProduct n b c ⟶ normalizedLocus n b) := by
  rw [← (normalizedProduct_isPullback n b c).isoPullback_hom_fst]
  infer_instance

/-- The original parameter product is Noetherian. -/
instance normalizedProduct_isNoetherian : IsNoetherian (normalizedProduct n b c) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
    (prod.fst : normalizedProduct n b c ⟶ normalizedLocus n b)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
    (prod.fst : normalizedProduct n b c ⟶ normalizedLocus n b)

/-- The full curve-comparison scheme is Noetherian. -/
instance productComparisonScheme_isNoetherian :
    IsNoetherian (productComparisonScheme n b c) where
  toIsLocallyNoetherian :=
    LocallyOfFiniteType.isLocallyNoetherian (productComparisonStructure n b c)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (productComparisonStructure n b c)

/-- The actual subgroup-preserving comparison scheme is Noetherian. -/
instance productSubgroupScheme_isNoetherian : IsNoetherian (productSubgroupScheme n b c) where
  toIsLocallyNoetherian :=
    LocallyOfFiniteType.isLocallyNoetherian (productSubgroupStructure n b c)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (productSubgroupStructure n b c)

/-- The finite disjoint source is Noetherian. -/
instance normalizedDisjointSource_isNoetherian : IsNoetherian (normalizedDisjointSource n) where
  toIsLocallyNoetherian := (isLocallyNoetherian_iff_openCover
    (sigmaOpenCover (normalizedLocus n))).mpr fun i ↦ by
      simpa only [sigmaOpenCover_X] using
        (inferInstance : IsLocallyNoetherian (normalizedLocus n i))
  toCompactSpace := (sigmaMk (normalizedLocus n)).compactSpace

/-- All four original comparison components form a Noetherian full arrow scheme. -/
instance disjointComparisonArrows_isNoetherian : IsNoetherian (disjointComparisonArrows n) where
  toIsLocallyNoetherian := (isLocallyNoetherian_iff_openCover
    (sigmaOpenCover (fun p : Bool × Bool ↦ productSubgroupScheme n p.1 p.2))).mpr
      fun i ↦ by
        simpa only [sigmaOpenCover_X] using
          (inferInstance : IsLocallyNoetherian (productSubgroupScheme n i.1 i.2))
  toCompactSpace :=
    (sigmaMk (fun p : Bool × Bool ↦ productSubgroupScheme n p.1 p.2)).compactSpace

/-- Every original full relation domain is compact, including saturated affine source domains. -/
theorem disjointComparisonSource_preimage_isCompact (V : (normalizedDisjointSource n).Opens) :
    IsCompact (disjointComparisonSource n ⁻¹ᵁ V : Set (disjointComparisonArrows n)) :=
  NoetherianSpace.isCompact _

end FLT.Mazur.CyclicCharacteristicAtlas

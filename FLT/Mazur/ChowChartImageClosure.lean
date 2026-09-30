/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowSourceClosure
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# Projective closures of the Chow charts

Restrict the scheme-theoretic source closure to each original affine chart,
and take its image in the chart's projective space. The restricted chart is
an open, schematically dense subscheme of this proper image. The common open
factors through each image and remains schematically dense there.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow.ChartData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (D : ChartData f) [LocallyOfFiniteType f] [QuasiCompact f]

/-- The original chart pulled back to the scheme-theoretic source closure. -/
def sourceChart (i : D.Index) : D.sourceClosure.Opens :=
  D.sourceClosureι ⁻¹ᵁ D.opens i

/-- The closed comparison with the original affine chart. -/
def sourceChartToChart (i : D.Index) : (D.sourceChart i).toScheme ⟶ (D.opens i).toScheme :=
  D.sourceClosureι ∣_ D.opens i

instance sourceChartToChart_isClosedImmersion (i : D.Index) :
    IsClosedImmersion (D.sourceChartToChart i) := by
  dsimp [sourceChartToChart]
  infer_instance

/-- The projective immersion of the actual restricted source closure. -/
def sourceChartToProjective (i : D.Index) :
    (D.sourceChart i).toScheme ⟶ ProjectiveSpace.space k (Fin (D.dimension i + 1)) :=
  D.sourceChartToChart i ≫ D.immersion i

instance sourceChartToProjective_isImmersion (i : D.Index) :
    IsImmersion (D.sourceChartToProjective i) := by
  dsimp [sourceChartToProjective]
  infer_instance

instance sourceChartToProjective_quasiCompact (i : D.Index) :
    QuasiCompact (D.sourceChartToProjective i) := by
  let _noetherian := source_isNoetherian f
  have : IsNoetherian D.sourceClosure := source_isNoetherian D.sourceClosureι
  have : NoetherianSpace (D.sourceChart i).toScheme :=
    NoetherianSpace.set (D.sourceChart i : Set D.sourceClosure)
  exact quasiCompact_of_noetherianSpace_source _

omit [LocallyOfFiniteType f] [QuasiCompact f] in
/-- The common open lands in every restricted chart of the source closure. -/
lemma commonToSourceClosure_range_sourceChart (i : D.Index) :
    Set.range D.commonToSourceClosure ⊆ Set.range (D.sourceChart i).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change D.sourceClosureι (D.commonToSourceClosure x) ∈ D.opens i
  rw [← Scheme.Hom.comp_apply, D.commonToSourceClosure_ι]
  exact (iInf_le D.opens i) x.property

/-- The common-open map to the restricted source chart. -/
def commonToSourceChart (i : D.Index) : D.common.toScheme ⟶ (D.sourceChart i).toScheme :=
  IsOpenImmersion.lift (D.sourceChart i).ι D.commonToSourceClosure
    (D.commonToSourceClosure_range_sourceChart i)

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma commonToSourceChart_ι (i : D.Index) :
    D.commonToSourceChart i ≫ (D.sourceChart i).ι = D.commonToSourceClosure :=
  IsOpenImmersion.lift_fac _ _ _

instance commonToSourceChart_isOpenImmersion (i : D.Index) :
    IsOpenImmersion (D.commonToSourceChart i) := by
  dsimp [commonToSourceChart]
  infer_instance

/-- Restricting the schematically dense common open along an open immersion
preserves schematic density, including nonreduced source schemes. -/
instance commonToSourceChart_schemeTheoreticallyDominant (i : D.Index) :
    IsSchemeTheoreticallyDominant (D.commonToSourceChart i) := by
  let _noetherian := source_isNoetherian f
  have : NoetherianSpace D.common.toScheme := NoetherianSpace.set (D.common : Set X)
  have : QuasiCompact D.commonToSourceClosure := quasiCompact_of_noetherianSpace_source _
  exact IsSchemeTheoreticallyDominant.of_isPullback
    (IsOpenImmersion.isPullback_lift_id D.commonToSourceClosure (D.sourceChart i).ι
      (D.commonToSourceClosure_range_sourceChart i)).flip

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma commonToSourceChart_toChart (i : D.Index) :
    D.commonToSourceChart i ≫ D.sourceChartToChart i = commonToChart D.opens i := by
  rw [← cancel_mono (D.opens i).ι, Category.assoc]
  rw [sourceChartToChart, morphismRestrict_ι, ← Category.assoc]
  change (D.commonToSourceChart i ≫ (D.sourceChart i).ι) ≫ _ = _
  rw [D.commonToSourceChart_ι, D.commonToSourceClosure_ι, commonToChart_ι]
  rfl

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma commonToSourceChart_toProjective (i : D.Index) :
    D.commonToSourceChart i ≫ D.sourceChartToProjective i = D.commonToProjective i := by
  simp [sourceChartToProjective, ← Category.assoc, commonToProjective]

/-- The scheme-theoretic projective image of the restricted chart. -/
def chartImage (i : D.Index) : Scheme.{u} := (D.sourceChartToProjective i).image

/-- The canonical closed embedding of the chart image in projective space. -/
def chartImageι (i : D.Index) :
    D.chartImage i ⟶ ProjectiveSpace.space k (Fin (D.dimension i + 1)) :=
  (D.sourceChartToProjective i).imageι

instance chartImageι_isClosedImmersion (i : D.Index) :
    IsClosedImmersion (D.chartImageι i) := by
  dsimp [chartImageι]
  infer_instance

/-- The restricted affine chart as an open subscheme of its projective image. -/
def sourceChartToImage (i : D.Index) : (D.sourceChart i).toScheme ⟶ D.chartImage i :=
  (D.sourceChartToProjective i).toImage

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma sourceChartToImage_ι (i : D.Index) :
    D.sourceChartToImage i ≫ D.chartImageι i = D.sourceChartToProjective i :=
  (D.sourceChartToProjective i).toImage_imageι

instance sourceChartToImage_isOpenImmersion (i : D.Index) :
    IsOpenImmersion (D.sourceChartToImage i) := by
  dsimp [sourceChartToImage]
  infer_instance

instance sourceChartToImage_schemeTheoreticallyDominant (i : D.Index) :
    IsSchemeTheoreticallyDominant (D.sourceChartToImage i) :=
  toImage_schemeTheoreticallyDominant _

/-- The common-open component factored through the constructed chart image. -/
def commonToChartImage (i : D.Index) : D.common.toScheme ⟶ D.chartImage i :=
  D.commonToSourceChart i ≫ D.sourceChartToImage i

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma commonToChartImage_ι (i : D.Index) :
    D.commonToChartImage i ≫ D.chartImageι i = D.commonToProjective i := by
  simp [commonToChartImage, Category.assoc]

instance commonToChartImage_isOpenImmersion (i : D.Index) :
    IsOpenImmersion (D.commonToChartImage i) := by
  dsimp [commonToChartImage]
  infer_instance

instance commonToChartImage_schemeTheoreticallyDominant (i : D.Index) :
    IsSchemeTheoreticallyDominant (D.commonToChartImage i) := by
  dsimp [commonToChartImage]
  infer_instance

/-- The closed chart image has its original field as base. -/
def chartImageProjection (i : D.Index) : D.chartImage i ⟶ Spec (.of k) :=
  D.chartImageι i ≫ ProjectiveSpace.baseProjection k (Fin (D.dimension i + 1))

instance chartImageProjection_isProper (i : D.Index) :
    IsProper (D.chartImageProjection i) := by
  dsimp [chartImageProjection]
  infer_instance

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma commonToChartImage_projection (i : D.Index) :
    D.commonToChartImage i ≫ D.chartImageProjection i = D.common.ι ≫ f := by
  simp [chartImageProjection, ← Category.assoc]

/-- Schematic density identifies the chart image ideal with the kernel of
the original common-open component, ready for product factorization. -/
lemma chartImageι_ker (i : D.Index) :
    (D.chartImageι i).ker = (D.commonToProjective i).ker := by
  rw [← D.commonToChartImage_ι i, Scheme.Hom.ker_comp,
    (D.commonToChartImage i).ker_eq_bot, Scheme.IdealSheafData.map_bot]

end FLT.Mazur.Chow.ChartData

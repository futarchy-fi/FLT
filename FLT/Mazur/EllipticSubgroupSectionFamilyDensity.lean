/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureProduct
public import FLT.Mazur.SchemeFlatProductDensity
public import FLT.Mazur.SchemeSectionFamilyProduct

/-!
# Schematic density of the integral section family

The actual section family is schematically dense and flat over the valuation
ring. Over a DVR its product comparison is therefore schematically dense.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The original integral subgroup sections cover the actual closure. -/
instance closureSectionsMap_surjective : Surjective (closureSectionsMap A W H) := by
  constructor
  intro x
  obtain ⟨P, y, rfl⟩ := integralSections_cover A W H x
  refine ⟨Sigma.ι (fun _ : H => Spec (.of A)) P y, ?_⟩
  exact congrArg (fun f : Spec (.of A) ⟶ gluedClosure A W H 1 2 => f y)
    (closureSectionsMap_point A W H P)

/-- The integral family is quasi-compact. -/
instance closureSectionsMap_quasiCompact : QuasiCompact (closureSectionsMap A W H) := by
  have : IsAffine (∐ fun _ : H => Spec (.of A)) := inferInstance
  infer_instance

/-- Integral sections detect all equations on the reduced closure. -/
instance closureSectionsMap_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (closureSectionsMap A W H) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

/-- The structural map of the section family is flat. -/
instance closureSectionsMap_toBase_flat :
    Flat (closureSectionsMap A W H ≫ closureToBase A W H 1 2) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (sigmaOpenCover (fun _ : H => Spec (.of A)))
  intro P
  change Flat (Sigma.ι (fun _ : H => Spec (.of A)) P ≫
    closureSectionsMap A W H ≫ closureToBase A W H 1 2)
  rw [closureSectionsMap_point_assoc, integralSection_toBase]
  infer_instance

/-- The product of the actual section-family morphisms. -/
def closureSectionsProductMap :
    pullback (closureSectionsMap A W H ≫ closureToBase A W H 1 2)
      (closureSectionsMap A W H ≫ closureToBase A W H 1 2) ⟶ closureProduct A W H :=
  pullback.map _ _ _ _ (closureSectionsMap A W H) (closureSectionsMap A W H)
    (𝟙 _) (by simp) (by simp)

/-- Over a DVR the product family is schematically dense, by proved flat base change. -/
instance closureSectionsProductMap_isSchemeTheoreticallyDominant [IsDedekindDomain A] :
    IsSchemeTheoreticallyDominant (closureSectionsProductMap A W H) :=
  SchemeFlatProductDensity.product_dense _ _ _ _

/-- The paired copies of the base are the product of the section-family sources. -/
def closureSectionSourceProductIso : (∐ fun _ : H × H => Spec (.of A)) ≅
    pullback (closureSectionsMap A W H ≫ closureToBase A W H 1 2)
      (closureSectionsMap A W H ≫ closureToBase A W H 1 2) :=
  (SchemeSectionFamilyProduct.iso (Spec (.of A)) H H).trans
    (pullback.congrHom (closureSectionsMap_toBase A W H).symm
      (closureSectionsMap_toBase A W H).symm)

/-- First projection of the paired-source comparison. -/
@[reassoc] theorem closureSectionSourceProductIso_fst :
    (closureSectionSourceProductIso A W H).hom ≫ pullback.fst _ _ =
      Sigma.desc fun p : H × H => Sigma.ι (fun _ : H => Spec (.of A)) p.1 := by
  simp only [closureSectionSourceProductIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id,
    SchemeSectionFamilyProduct.iso_hom_fst]

/-- Second projection of the paired-source comparison. -/
@[reassoc] theorem closureSectionSourceProductIso_snd :
    (closureSectionSourceProductIso A W H).hom ≫ pullback.snd _ _ =
      Sigma.desc fun p : H × H => Sigma.ι (fun _ : H => Spec (.of A)) p.2 := by
  simp only [closureSectionSourceProductIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    SchemeSectionFamilyProduct.iso_hom_snd]

end FLT.Mazur.EllipticSubgroupChart

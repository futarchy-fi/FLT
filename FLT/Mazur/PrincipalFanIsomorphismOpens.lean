/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanIsomorphismLimits

/-!
# Compatible open immersions into the shared ambient chart

All finite overlap targets embed into the same ambient source scheme. The
images are their prescribed basic opens, and the embeddings commute both
with stage transitions and with the original principal-open projections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  (a : ι → A) (b : ∀ i, B i)
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))

/-- The principal inclusions form a natural map to the single ambient chart system. -/
def principalIsoFanInclusion (i : ι) :
    (principalIsoFanSourceDiagram a b e i).op ⋙ Scheme.Spec ⟶
      (principalIsoFanChartDiagram a b e).op ⋙ Scheme.Spec where
  app x := PrincipalLocalizationSquare.inclusion
    (Ideal.Quotient.mk _ (principalRepresentative R A (a i)))
  naturality x y h := by
    exact (PrincipalLocalizationSquare.condition
      (FiniteRelationModel.transition R (relationIdeal R A) (leOfHom h.unop).1).toRingHom
      (Ideal.Quotient.mk _ (principalRepresentative R A (a i)))).symm

/-- Every target overlaps the same ambient diagram by an actual open immersion. -/
def principalIsoFanOpenMap (i : ι) :
    (principalIsoFanTargetDiagram a b e i).op ⋙ Scheme.Spec ⟶
      (principalIsoFanChartDiagram a b e).op ⋙ Scheme.Spec :=
  (principalIsoFanSchemeIso a b e i).hom ≫ principalIsoFanInclusion a b e i

/-- The explicit coordinate isomorphism at one finite stage. -/
def principalIsoFanStageIso (x : PrincipalFanIsomorphismStage a b e) (i : ι) :
    Spec (.of (PrincipalStage R (B i) (b i) (x.val.target i))) ≅
      Spec (.of (PrincipalStage R A (a i) x.val.source)) :=
  Scheme.Spec.mapIso ((principalFanStageEquiv a b e x i).toRingEquiv.toCommRingCatIso.op)

/-- The concrete open immersion of one finite overlap target into the common chart. -/
def principalIsoFanOpen (x : PrincipalFanIsomorphismStage a b e) (i : ι) :
    Spec (.of (PrincipalStage R (B i) (b i) (x.val.target i))) ⟶
      Spec (.of (Stage R A x.val.source)) :=
  (principalIsoFanStageIso a b e x i).hom ≫ PrincipalLocalizationSquare.inclusion
    (Ideal.Quotient.mk (FiniteRelationModel.relations (relationIdeal R A) x.val.source)
      (principalRepresentative R A (a i)))

/-- All constructed finite overlap embeddings are open immersions. -/
instance principalIsoFanOpen_isOpenImmersion (x : PrincipalFanIsomorphismStage a b e) (i : ι) :
    IsOpenImmersion (principalIsoFanOpen a b e x i) := by
  dsimp only [principalIsoFanOpen]
  infer_instance

/-- Each overlap has precisely its intended basic-open image in the shared chart. -/
theorem principalIsoFanOpen_opensRange (x : PrincipalFanIsomorphismStage a b e) (i : ι) :
    (principalIsoFanOpen a b e x i).opensRange =
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk
        (FiniteRelationModel.relations (relationIdeal R A) x.val.source)
          (principalRepresentative R A (a i))) := by
  dsimp only [principalIsoFanOpen]
  rw [Scheme.Hom.opensRange_comp_of_isIso, PrincipalLocalizationSquare.inclusion_opensRange]

/-- The coordinate identifications commute with the original principal projections. -/
theorem principalIsoFanSchemeIso_fac (x : PrincipalFanIsomorphismStage a b e) (i : ι) :
    Spec.map (CommRingCat.ofHom (e i).toAlgHom.toRingHom) ≫
        (principalIsoFanSourceCone a b e i).π.app (.op x) =
      (principalIsoFanTargetCone a b e i).π.app (.op x) ≫
        (principalIsoFanSchemeIso a b e i).hom.app (.op x) := by
  change Spec.map (CommRingCat.ofHom (e i).toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (principalStageMap R A (a i) x.val.source).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (principalStageMap R (B i) (b i) (x.val.target i)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (x.val.hom i).toRingHom)
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (x.val.fac i).symm

/-- The finite overlap embeddings recover the original open inclusions into the full chart. -/
theorem principalIsoFanOpen_fac (x : PrincipalFanIsomorphismStage a b e) (i : ι) :
    (principalIsoFanTargetCone a b e i).π.app (.op x) ≫ principalIsoFanOpen a b e x i =
      Spec.map (CommRingCat.ofHom (e i).toAlgHom.toRingHom) ≫
        PrincipalLocalizationSquare.inclusion (a i) ≫
          (principalIsoFanChartCone a b e).π.app (.op x) := by
  let j : Spec (.of (PrincipalStage R A (a i) x.val.source)) ⟶
      Spec (.of (Stage R A x.val.source)) :=
    PrincipalLocalizationSquare.inclusion
      (Ideal.Quotient.mk _ (principalRepresentative R A (a i)))
  let f : Spec (.of (Localization.Away (b i))) ⟶ Spec (.of (Localization.Away (a i))) :=
    Spec.map (CommRingCat.ofHom (e i).toAlgHom.toRingHom)
  let p : Spec (.of (Localization.Away (b i))) ⟶
      Spec (.of (PrincipalStage R (B i) (b i) (x.val.target i))) :=
    (principalIsoFanTargetCone a b e i).π.app (.op x)
  let q : Spec (.of (Localization.Away (a i))) ⟶
      Spec (.of (PrincipalStage R A (a i) x.val.source)) :=
    (principalIsoFanSourceCone a b e i).π.app (.op x)
  let d : Spec (.of (PrincipalStage R (B i) (b i) (x.val.target i))) ⟶
      Spec (.of (PrincipalStage R A (a i) x.val.source)) :=
    (principalIsoFanSchemeIso a b e i).hom.app (.op x)
  have hf : f ≫ q = p ≫ d := principalIsoFanSchemeIso_fac a b e x i
  have hq : q ≫ j = PrincipalLocalizationSquare.inclusion (a i) ≫
      (principalIsoFanChartCone a b e).π.app (.op x) :=
    (principalProjection_isPullback R A (a i) x.val.source).w
  change p ≫ d ≫ j = f ≫ _
  rw [← Category.assoc, ← hf, Category.assoc, hq]

end FLT.Mazur.FiniteTypeRelationModel

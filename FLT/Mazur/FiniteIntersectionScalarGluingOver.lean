/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionGluingBaseChange
public import FLT.Mazur.FiniteIntersectionScalarGluingRecovery

/-!
# Structural compatibility of scalar gluing recovery

The recovery isomorphism of the tensor-extended gluing respects the given
map to `Spec A`. This identifies the original scheme, over its actual
base, with the coefficient pullback of the glued integer model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u v

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra S A]
  {X : Scheme.{u}} {ι : Type v} [Finite ι] (U : ι → X.Opens)
  (p : X ⟶ Spec (.of A)) [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
  (hcover : iSup U = ⊤) (D : NonemptyChartSet ι ⥤ CommAlgCat S)
  [∀ a b (f : a ⟶ b),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom))]
  (hp : ∀ (r s t : NonemptyChartSet ι) (hrs : r ≤ s) (hrt : r ≤ t),
    IsPullback
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_left s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE (le_unionChartSet_right s t))).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrs)).hom.toRingHom))
      (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrt)).hom.toRingHom)))
  (e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] (finiteIntersectionSectionDiagram U p).obj a)
  (he : ∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
    (affineScalarExtensionHom (S := A) (D.map f).hom) =
    ((finiteIntersectionSectionDiagram U p).map f).hom.comp (e a).toAlgHom)

omit [Finite ι] in
/-- The actual intersection's coordinate isomorphism respects its structural map. -/
@[reassoc]
theorem finiteIntersectionSectionSpecIso_over (a : NonemptyChartSet ι) :
    (finiteIntersectionSectionSpecIso U p hU a).hom ≫
      (affineIntersectionBaseCocone (finiteIntersectionSectionDiagram U p)).ι.app
        (Opposite.op a) = (finiteIntersectionOpen U a).ι ≫ p := by
  let := finiteIntersectionOverDiagram_isAffine U p hU a
  exact affineBaseSectionsSpecIso_over A ((finiteIntersectionOverDiagram U p).obj (Opposite.op a))

/-- The recovered glued scheme retains the specified structural map. -/
@[reassoc]
theorem finiteIntersectionScalarGluingIso_over :
    (finiteIntersectionScalarGluingIso U p hU hcover D hp e he).hom ≫ p =
      affineIntersectionGluedToBase (affineIntersectionScalarExtension (A := A) D)
        (affineIntersectionScalarExtension_isPullback D hp) := by
  let F := affineIntersectionSchemeDiagram (affineIntersectionScalarExtension (A := A) D)
  let := intersectionDiagram_isLocallyDirected F
    (affineIntersectionScalarExtension_isPullback D hp)
  apply (Scheme.IsLocallyDirected.isColimit F).hom_ext
  intro a
  simp only [finiteIntersectionScalarGluingIso, intersectionDiagramGluingIsoOfNatIso,
    finiteIntersectionGluingIso, Iso.trans_hom, Category.assoc,
    IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
    colimit.cocone_ι, HasColimit.ι_isoOfNatIso_hom_assoc,
    colimit.comp_coconePointUniqueUpToIso_hom_assoc]
  change (affineIntersectionScalarExtensionSpecIso D
    (finiteIntersectionSectionDiagram U p) e he).hom.app a ≫
    (finiteIntersectionSectionSpecIso U p hU a.unop).inv ≫
      (finiteIntersectionOpen U a.unop).ι ≫ p = _
  rw [← finiteIntersectionSectionSpecIso_over U p hU a.unop, Iso.inv_hom_id_assoc]
  change _ = (Scheme.IsLocallyDirected.cocone F).ι.app a ≫
    (Scheme.IsLocallyDirected.isColimit F).desc
      (affineIntersectionBaseCocone (affineIntersectionScalarExtension (A := A) D))
  rw [IsColimit.fac]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (e a.unop).symm.toAlgHom.comp_algebraMap

/-- Pulling back the constructed integer-model gluing recovers the covered scheme. -/
def finiteIntersectionModelPullbackIso :
    pullback (affineIntersectionGluedToBase D hp)
      (Spec.map (CommRingCat.ofHom (algebraMap S A))) ≅ X :=
  (affineIntersectionGluingPullbackIso D hp).symm ≪≫
    finiteIntersectionScalarGluingIso U p hU hcover D hp e he

/-- Recovery from the model pullback is an isomorphism over `Spec A`. -/
@[reassoc (attr := simp)]
theorem finiteIntersectionModelPullbackIso_over :
    (finiteIntersectionModelPullbackIso U p hU hcover D hp e he).hom ≫ p = pullback.snd _ _ := by
  simp only [finiteIntersectionModelPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    finiteIntersectionScalarGluingIso_over]
  rw [← affineIntersectionGluingPullbackIso_snd D hp, Iso.inv_hom_id_assoc]

end FLT.Mazur.Approximation

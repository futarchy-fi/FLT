/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartBaseChange
public import FLT.Mazur.WeierstrassIntegralCoefficientMap

/-!
# Cartesian coefficient squares for the normalized cubic charts

The explicit tensor algebra equivalence identifies each specialized chart
with the categorical fiber product of its original chart and coefficient
spectrum. Both projections are the previously constructed morphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j : Fin 3)

/-- The specialized chart as the actual categorical coefficient pullback. -/
def chartCoefficientPullbackIso : chartScheme (W.map (algebraMap R S)) j ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (chartStructure W j) :=
  Scheme.Spec.mapIso (chartBaseChangeEquiv S W j).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R S (Coordinate W j)).symm

/-- The pullback comparison retains the new coefficient structure. -/
@[reassoc] theorem chartCoefficientPullbackIso_fst :
    (chartCoefficientPullbackIso (S := S) W j).hom ≫ pullback.fst _ _ =
      chartStructure (W.map (algebraMap R S)) j := by
  simp only [chartCoefficientPullbackIso, chartStructure, Iso.trans_hom, Iso.symm_hom,
    Category.assoc,
    pullbackSpecIso_inv_fst']
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (chartBaseChangeEquiv S W j).commutes

/-- The other projection is the actual coefficient map on normalized cubic coordinates. -/
@[reassoc] theorem chartCoefficientPullbackIso_snd :
    (chartCoefficientPullbackIso (S := S) W j).hom ≫ pullback.snd _ _ =
      chartCoefficientMorphism W j := by
  simp only [chartCoefficientPullbackIso, chartStructure, Iso.trans_hom, Iso.symm_hom,
    Category.assoc,
    pullbackSpecIso_inv_snd]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change chartBaseChangeForward S W j (Algebra.TensorProduct.includeRight a) =
    chartCoefficientMap W j a
  rw [Algebra.TensorProduct.includeRight_apply, chartBaseChangeForward_tmul, one_smul]

/-- Each actual normalized chart commutes with arbitrary coefficient base change. -/
theorem chartCoefficient_isPullback :
    IsPullback (chartCoefficientMorphism (S := S) W j)
      (chartStructure (W.map (algebraMap R S)) j) (chartStructure W j)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply IsPullback.flip
  apply IsPullback.of_iso_pullback _ (chartCoefficientPullbackIso W j)
    (chartCoefficientPullbackIso_fst W j) (chartCoefficientPullbackIso_snd W j)
  constructor
  rw [← chartCoefficientPullbackIso_fst, ← chartCoefficientPullbackIso_snd,
    Category.assoc, Category.assoc, pullback.condition]

end FLT.Mazur.WeierstrassIntegralChart

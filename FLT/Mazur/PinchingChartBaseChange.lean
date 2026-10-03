/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonScalarExtension
public import FLT.Mazur.PolygonNodeScalarExtension
public import Mathlib.AlgebraicGeometry.Pullbacks
/-!
# Pinching charts after extension of the coefficient ring

The actual scheme pullbacks of the node and one-gon charts are their charts
over the new coefficient ring. Both projections retain their specified maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
namespace FLT.Mazur.PinchingChartBaseChange
open PolygonNodeEqualizer PolygonNodePresentation
open PolygonNodeScalarExtension (nodeTensorIso)
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
/-- The affine base-change morphism. -/
def parameter : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))
/-- The node structure morphism. -/
def nodeBase : Spec (.of (A (R := R))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (A (R := R))))
/-- The one-gon chart structure morphism. -/
def oneGonBase : Spec (.of (B (R := R))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (B (R := R))))

/-- The node chart over the extended coefficient ring. -/
def nodeProductIso : pullback (parameter R S) (nodeBase R) ≅ Spec (.of (A (R := S))) :=
  pullbackSpecIso R S (A (R := R)) ≪≫ Scheme.Spec.mapIso
    (nodeTensorIso (R := R) (S := S)).symm.toRingEquiv.toCommRingCatIso.op

/-- The one-gon chart over the extended coefficient ring. -/
def oneGonProductIso : pullback (parameter R S) (oneGonBase R) ≅ Spec (.of (B (R := S))) :=
  pullbackSpecIso R S (B (R := R)) ≪≫ Scheme.Spec.mapIso
    (OneGonScalarExtension.oneGonTensorIso (R := R) (S := S)).symm.toRingEquiv.toCommRingCatIso.op

@[reassoc (attr := simp)] theorem nodeProductIso_inv_fst :
    (nodeProductIso R S).inv ≫ pullback.fst _ _ = nodeBase S := by
  change Spec.map (CommRingCat.ofHom
      (nodeTensorIso (R := R) (S := S)).toAlgHom.toRingHom) ≫
    (pullbackSpecIso R S (A (R := R))).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact AlgHom.comp_algebraMap (nodeTensorIso.toAlgHom)

@[reassoc (attr := simp)] theorem oneGonProductIso_inv_fst :
    (oneGonProductIso R S).inv ≫ pullback.fst _ _ = oneGonBase S := by
  change Spec.map (CommRingCat.ofHom
      (OneGonScalarExtension.oneGonTensorIso (R := R) (S := S)).toAlgHom.toRingHom) ≫
    (pullbackSpecIso R S (B (R := R))).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact AlgHom.comp_algebraMap (OneGonScalarExtension.oneGonTensorIso.toAlgHom)

@[reassoc (attr := simp)] theorem nodeProductIso_inv_snd :
    (nodeProductIso R S).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (PolygonNodeScalarExtension.coeffMap (R := R) (S := S)).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
      (nodeTensorIso (R := R) (S := S)).toAlgHom.toRingHom) ≫
    (pullbackSpecIso R S (A (R := R))).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact one_smul S (PolygonNodeScalarExtension.coeffMap p)

@[reassoc (attr := simp)] theorem oneGonProductIso_inv_snd :
    (oneGonProductIso R S).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (OneGonScalarExtension.coeffMap (R := R) (S := S)).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
      (OneGonScalarExtension.oneGonTensorIso (R := R) (S := S)).toAlgHom.toRingHom) ≫
    (pullbackSpecIso R S (B (R := R))).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact one_smul S (OneGonScalarExtension.coeffMap p)
end FLT.Mazur.PinchingChartBaseChange

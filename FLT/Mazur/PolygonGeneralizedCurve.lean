/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedEllipticCurve
public import FLT.Mazur.PolygonClassifiedFamily
public import FLT.Mazur.PolygonActionSmooth
public import FLT.Mazur.PolygonGeometricTranslations
public import FLT.Mazur.PolygonGroupPoints

/-!
# Specified polygons are generalized elliptic curves

The family, smooth-group identification, whole-curve action and geometric
rotation proofs are assembled without additional geometric hypotheses.
The rotation theorem includes every rational point of every geometric group.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonGeneralizedCurve
open PolygonPinching PolygonUniversalAction PolygonActionFieldExtension
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- All translations of the actual field-extended group rotate the graph. -/
theorem field_rotations (L : Type) [Field L] [Algebra K L] :
    let := polygon_lfp K n hn p q h
    GeneralizedCurveGraph.FiberRotations (act K n hn p q h)
      (ProjectiveLineProductCharts.parameterToBase K L) := by
  let := polygon_lfp K n hn p q h
  let := polygon_lfp L n hn (normalization K L n p) (nodeMap K L n q)
    (cocone K L n hn p q h)
  refine ⟨n, hn, PolygonActionGraph.vertices L n hn _ _ (cocone K L n hn p q h),
    PolygonActionGraph.edges L n hn _ _ (cocone K L n hn p q h),
    PolygonActionGraph.incidence L n hn _ _ (cocone K L n hn p q h), ?_⟩
  intro x
  obtain ⟨a, b, hab⟩ := PolygonGroupPoints.groupPoint_surjective L n
    (x ≫ (groupIso K L n).inv)
  change PolygonActionTranslation.groupPoint L n a b = x ≫ (groupIso K L n).inv at hab
  have hx : PolygonActionTranslation.groupPoint L n a b ≫ (groupIso K L n).hom = x := by
    rw [hab, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [← hx]
    exact PolygonGeometricTranslations.component_rotation K L n hn p q h a b i
  · intro j
    rw [← hx]
    exact PolygonGeometricTranslations.node_rotation K L n hn p q h a b j

/-- The polygon satisfies DR's graph condition for arbitrary geometric base points. -/
theorem geometric_rotations : letI := polygon_lfp K n hn p q h
    GeneralizedCurveGraph.GeometricRotations (act K n hn p q h) := by
  let := polygon_lfp K n hn p q h
  intro L _ _ g _
  let := (Spec.preimage g).hom.toAlgebra
  have hg : ProjectiveLineProductCharts.parameterToBase K L = g := Spec.map_preimage g
  change GeneralizedCurveGraph.FiberRotations (act K n hn p q h) g
  rw [← hg]
  exact field_rotations K n hn p q h L

/-- Every specified positive polygon is a relative generalized elliptic curve. -/
def curve : GeneralizedEllipticCurve (Spec (.of K)) where
  curve := C
  family := PolygonClassifiedFamily.family K n hn p q h
  group := G K n
  smoothIso := by
    let := polygon_lfp K n hn p q h
    exact (PolygonPinching.smoothIso K n hn p q h).symm
  act := act K n hn p q h
  unit_act := PolygonActionUnit.unit_act K n hn p q h
  assoc_act := PolygonActionAssociativity.assoc_act K n hn p q h
  restriction := by
    let := polygon_lfp K n hn p q h
    exact PolygonActionSmooth.model_restriction K n hn p q h
  rotations := geometric_rotations K n hn p q h

/-- The action, expressed on the actual smooth open, restricts to its multiplication. -/
theorem smooth_restriction :
    let := polygon_lfp K n hn p q h
    let := smoothGrpObj K n hn p q h
    let := smoothCommGrpObj K n hn p q h
    ((PolygonPinching.smoothIso K n hn p q h).hom ⊗ₘ PolygonActionSmooth.smoothι K) ≫
      (curve K n hn p q h).act =
        MonObj.mul (X := smoothPolygon K (C := C)) ≫ PolygonActionSmooth.smoothι K := by
  let := polygon_lfp K n hn p q h
  exact PolygonActionSmooth.smooth_restriction K n hn p q h

end FLT.Mazur.PolygonGeneralizedCurve

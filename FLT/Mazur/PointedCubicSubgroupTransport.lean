/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePointedCubicFamily
public import FLT.Mazur.CompatibleSubgroupCyclic
public import FLT.Mazur.CompatibleSubgroupAmple

/-!
# The original finite subgroup in a full pointed cubic chart

Transport retains the subgroup scheme itself and changes only its embedding
through the full original curve comparison. Cyclicity and ampleness follow
from that compatible isomorphism, with no new subgroup hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
  {E : GeneralizedEllipticCurve S} {n : ℕ} (H : E.FiniteSubgroup n)
  (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (e : E.curve.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = E.curve.hom ≫ S.toSpecΓ)
  (hs : E.identitySection.left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W)

/-- The actual original subgroup viewed in the pointed cubic, with unchanged carrier. -/
def pointedCubicSubgroup : (pointedCubicFamily W).FiniteSubgroup n :=
  H.transport (pointedCubicFamilyIso W E e he hs)

/-- The subgroup and original full family have an actual compatible isomorphism. -/
def pointedCubicSubgroupIso : CompatibleIso H (pointedCubicSubgroup H W e he hs) where
  curve := pointedCubicFamilyIso W E e he hs
  subgroup := Iso.refl H.carrier
  isMonHom := inferInstanceAs (IsMonHom (𝟙 H.carrier))
  compatible := by
    change H.curveMap ≫ _ = (𝟙 H.carrier) ≫
      (H.transport (pointedCubicFamilyIso W E e he hs)).curveMap
    rw [Category.id_comp, transport_curveMap]

/-- The retained subgroup embedding projects through the exact original complete cubic map. -/
@[reassoc] theorem pointedCubicSubgroup_curveMap_fst :
    (pointedCubicSubgroup H W e he hs).curveMap.left ≫
      pullback.fst (integralCurveStructure W) S.toSpecΓ = H.curveMap.left ≫ e.hom := by
  change (H.transport (pointedCubicFamilyIso W E e he hs)).curveMap.left ≫ _ = _
  rw [transport_curveMap, Over.comp_left, Category.assoc, pointedCubicFamilyIso_curve_fst]

/-- The pointed cubic retains exactly the cyclicity of the original subgroup. -/
theorem pointedCubicSubgroup_cyclic_iff :
    (pointedCubicSubgroup H W e he hs).IsCyclic ↔ H.IsCyclic :=
  (pointedCubicSubgroupIso H W e he hs).isCyclic_iff.symm

/-- The pointed cubic retains exactly the ampleness of the original subgroup divisor. -/
theorem pointedCubicSubgroup_ample_iff :
    (pointedCubicSubgroup H W e he hs).IsAmple ↔ H.IsAmple :=
  (pointedCubicSubgroupIso H W e he hs).isAmple_iff.symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleCurveTransport
public import FLT.Mazur.CyclicBoundaryAmpleAction

/-!
# Curve transport is functorial and equivariant on ample charts

Identity, composition and the common finite relabeling action are equalities
of the actual parameter maps. All original auxiliary and cyclic labels survive.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F G : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom] [IsSeparated G.group.hom]
  (e : E ≅ F) (d : F ≅ G) (n : ℕ) [NeZero n]

/-- Identity curve transport fixes every faithful boundary parameter. -/
theorem faithfulCurveTransport_id {U : Over S}
    (f : U ⟶ cyclicFaithfulParameter E.group n) :
    faithfulCurveTransport (Iso.refl E) n f = f := by
  apply (cancel_mono (cyclicFaithfulInclusion E.group n)).mp
  apply AuxiliaryLevel.homScheme_ext
  intro a
  simp only [Category.assoc, faithfulCurveTransport_value]
  change f ≫ cyclicFaithfulInclusion E.group n ≫
    AuxiliaryLevel.value E.group (Label n) a ≫ (𝟙 E.group) = _
  rw [Category.comp_id]

/-- Successive full curve comparisons transport exactly the same faithful parameter. -/
theorem faithfulCurveTransport_comp {U : Over S}
    (f : U ⟶ cyclicFaithfulParameter E.group n) :
    faithfulCurveTransport d n (faithfulCurveTransport e n f) =
      faithfulCurveTransport (e ≪≫ d) n f := by
  apply (cancel_mono (cyclicFaithfulInclusion G.group n)).mp
  apply AuxiliaryLevel.homScheme_ext
  intro a
  simp only [Category.assoc, faithfulCurveTransport_value, faithfulCurveTransport_value_assoc]
  rfl

/-- The actual faithful parameter isomorphisms compose in the original curve category. -/
theorem faithfulCurveTransportIso_comp :
    (faithfulCurveTransportIso e n).hom ≫ (faithfulCurveTransportIso d n).hom =
      (faithfulCurveTransportIso (e ≪≫ d) n).hom := by
  change faithfulCurveTransport e n (𝟙 _) ≫ faithfulCurveTransport d n (𝟙 _) = _
  rw [faithfulCurveTransport_natural, Category.comp_id, faithfulCurveTransport_comp]
  rfl

/-- Curve transport commutes with the original finite relabeling on faithful parameters. -/
theorem faithfulCurveTransport_relabel (a : RelabelGroup n) :
    faithfulRelabel E.group n a ≫ (faithfulCurveTransportIso e n).hom =
      (faithfulCurveTransportIso e n).hom ≫ faithfulRelabel F.group n a := by
  apply (cancel_mono (cyclicFaithfulInclusion F.group n)).mp
  apply AuxiliaryLevel.homScheme_ext
  intro j
  simp only [Category.assoc, faithfulRelabel_inclusion_assoc,
    faithfulRelabel_inclusion, action_value, action_value_assoc, faithfulCurveTransportIso,
    faithfulCurveTransport_value, Category.id_comp]

variable [SmoothOfRelativeDimension 1 E.group.hom]
  [SmoothOfRelativeDimension 1 F.group.hom] [SmoothOfRelativeDimension 1 G.group.hom]

/-- Identity curve transport fixes the actual ample scheme. -/
theorem ampleCurveTransport_id : ampleCurveTransport (Iso.refl E) n = 𝟙 _ := by
  apply (cancel_mono (ampleParameterOpen E n).ι).mp
  rw [ampleCurveTransport_inclusion]
  change _ ≫ (faithfulCurveTransport (Iso.refl E) n (𝟙 _)).left = _
  rw [faithfulCurveTransport_id, Over.id_left, Category.comp_id, Category.id_comp]

/-- Actual ample chart comparisons satisfy the full curve-composition cocycle. -/
theorem ampleCurveTransport_comp :
    ampleCurveTransport e n ≫ ampleCurveTransport d n = ampleCurveTransport (e ≪≫ d) n := by
  apply (cancel_mono (ampleParameterOpen G n).ι).mp
  rw [Category.assoc, ampleCurveTransport_inclusion, ampleCurveTransport_inclusion_assoc,
    ampleCurveTransport_inclusion]
  exact congrArg ((ampleParameterOpen E n).ι ≫ ·)
    (congrArg Over.Hom.left (faithfulCurveTransportIso_comp e d n))

/-- The ample chart comparison is equivariant for the original finite action. -/
theorem ampleCurveTransport_relabel (a : RelabelGroup n) :
    ampleRelabel E n a ≫ ampleCurveTransport e n =
      ampleCurveTransport e n ≫ ampleRelabel F n a := by
  apply (cancel_mono (ampleParameterOpen F n).ι).mp
  rw [Category.assoc, ampleCurveTransport_inclusion, ampleRelabel_inclusion_assoc,
    Category.assoc, ampleRelabel_inclusion, ampleCurveTransport_inclusion_assoc]
  exact congrArg ((ampleParameterOpen E n).ι ≫ ·)
    (congrArg Over.Hom.left (faithfulCurveTransport_relabel e n a))

end FLT.Mazur.CyclicBoundaryParameter

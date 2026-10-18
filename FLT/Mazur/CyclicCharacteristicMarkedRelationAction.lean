/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicMarkedRelation

/-!
# The common finite relabeling group acts on both actual marked relations

Normalization equivariance relabels both retained original subgroup parameters
at once. Inverse labels give actual scheme automorphisms of the kernel pairs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The common finite action preserves arbitrary-source marked comparisons on both charts. -/
theorem MarkedRelated.relabel {T : Scheme} {f g : T ⟶ locus n b}
    (h : MarkedRelated n b f g) (e : RelabelGroup n) :
    MarkedRelated n b (f ≫ (relabelAction n b e).hom)
      (g ≫ (relabelAction n b e).hom) := by
  apply (markedRelated_iff_normalization_eq n b _ _).mpr
  have he := congrArg (fun z ↦ z ≫ (normalizedRelabelAction n b e).hom)
    ((markedRelated_iff_normalization_eq n b f g).mp h)
  simpa only [Category.assoc, normalization_equivariant] using he

/-- Relabel both actual original parameters of a represented marked comparison. -/
def markedRelationRelabel (e : RelabelGroup n) : markedRelation n b ⟶ markedRelation n b :=
  markedRelationPoint n b
    (markedRelationFirst n b ≫ (relabelAction n b e).hom)
    (markedRelationSecond n b ≫ (relabelAction n b e).hom)
    (MarkedRelated.relabel n b
      ((markedRelated_iff_normalization_eq n b _ _).mpr (markedRelation_condition n b)) e)

/-- Relabeling retains the prescribed action on the original source parameter. -/
@[reassoc] theorem markedRelationRelabel_first (e : RelabelGroup n) :
    markedRelationRelabel n b e ≫ markedRelationFirst n b =
      markedRelationFirst n b ≫ (relabelAction n b e).hom :=
  markedRelationPoint_first n b _ _ _

/-- Relabeling retains the same action on the original target parameter. -/
@[reassoc] theorem markedRelationRelabel_second (e : RelabelGroup n) :
    markedRelationRelabel n b e ≫ markedRelationSecond n b =
      markedRelationSecond n b ≫ (relabelAction n b e).hom :=
  markedRelationPoint_second n b _ _ _

/-- Identity labels fix the whole represented marked relation. -/
theorem markedRelationRelabel_one : markedRelationRelabel n b 1 = 𝟙 _ := by
  apply markedRelation_hom_ext
  · rw [markedRelationRelabel_first, map_one, Category.id_comp]
    exact Category.comp_id _
  · rw [markedRelationRelabel_second, map_one, Category.id_comp]
    exact Category.comp_id _

/-- Multiplication of common relabelings is composition of actual relation morphisms. -/
theorem markedRelationRelabel_mul (e d : RelabelGroup n) :
    markedRelationRelabel n b (e * d) =
      markedRelationRelabel n b d ≫ markedRelationRelabel n b e := by
  apply markedRelation_hom_ext
  · simp only [markedRelationRelabel_first, Category.assoc,
      markedRelationRelabel_first_assoc, map_mul, Aut.Aut_mul_def, Iso.trans_hom]
  · simp only [markedRelationRelabel_second, Category.assoc,
      markedRelationRelabel_second_assoc, map_mul, Aut.Aut_mul_def, Iso.trans_hom]

/-- Inverse common labels yield actual inverse automorphisms of both relation schemes. -/
def markedRelationRelabelAut (e : RelabelGroup n) : Aut (markedRelation n b) where
  hom := markedRelationRelabel n b e
  inv := markedRelationRelabel n b e⁻¹
  hom_inv_id := by
    rw [← markedRelationRelabel_mul, inv_mul_cancel, markedRelationRelabel_one]
  inv_hom_id := by
    rw [← markedRelationRelabel_mul, mul_inv_cancel, markedRelationRelabel_one]

/-- The same finite group acts on both represented full marked relations. -/
def markedRelationRelabelAction : RelabelGroup n →* Aut (markedRelation n b) where
  toFun := markedRelationRelabelAut n b
  map_one' := by
    apply Aut.ext
    exact markedRelationRelabel_one n b
  map_mul' e d := by
    apply Aut.ext
    exact markedRelationRelabel_mul n b e d

end FLT.Mazur.CyclicCharacteristicAtlas

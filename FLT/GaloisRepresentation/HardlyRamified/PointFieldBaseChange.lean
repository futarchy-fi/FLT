/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import FLT.GroupScheme.LocalPointField
public import FLT.GroupScheme.ModelBaseChange

/-!
# Point fields after scalar extension

The field cut out by the restricted full point action is the compositum of the
new base field and the image of the global point field. The embedding used here
is the same chosen embedding as in absolute-Galois restriction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan.FiniteContinuousGaloisModule

variable (W : FiniteContinuousGaloisModule) (L : Type) [Field L] [CharZero L]

/-- The global point field embedded into the algebraic closure of the new base field. -/
def pointFieldEmbedding : W.pointField →ₐ[ℚ] AlgebraicClosure L where
  __ := (AlgebraicClosure.map (algebraMap ℚ L)).comp W.pointField.val.toRingHom
  commutes' := fun x ↦ AlgebraicClosure.map_algebraMap _ x

/-- The local restriction kernel cuts out exactly the compositum with the global point field. -/
theorem fixedField_restrictedPointActionKernel :
    IntermediateField.fixedField (W.pointActionKernel.comap
      (Field.absoluteGaloisGroup.map (algebraMap ℚ L)).toMonoidHom) =
      IntermediateField.adjoin L (Set.range (W.pointFieldEmbedding L)) := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup
    (IntermediateField.adjoin L (Set.range (W.pointFieldEmbedding L)))]
  congr 1
  ext σ
  rw [Subgroup.mem_comap, ← W.pointField_fixingSubgroup,
    IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      change σ (AlgebraicClosure.map (algebraMap ℚ L) y.1) = _
      exact (Field.absoluteGaloisGroup.lift_map (algebraMap ℚ L) σ y.1).symm.trans
        (congrArg (AlgebraicClosure.map (algebraMap ℚ L)) (h y.1 y.2))
    | algebraMap x => exact σ.commutes x
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | inv x _ hx => simp only [map_inv₀, hx]
    | mul x y _ _ hx hy => simp only [map_mul, hx, hy]
  · intro h x hx
    apply (AlgebraicClosure.map (algebraMap ℚ L)).injective
    exact (Field.absoluteGaloisGroup.lift_map (algebraMap ℚ L) σ x).trans
      (h _ (IntermediateField.subset_adjoin _ _ ⟨⟨x, hx⟩, rfl⟩))

end ThreeAdicPlan.FiniteContinuousGaloisModule

namespace ThreeAdicPlan.HasFiniteFlatModel

variable {R : Type} [CommRing R] [Algebra R ℚ]
  {W : FiniteContinuousGaloisModule} (M : HasFiniteFlatModel R W)
  (S L : Type) [CommRing S] [Field L] [CharZero L]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R ℚ L]

/-- The point field of the base-changed model is the scalar extension of the full point field. -/
theorem localPointField_baseChange :
    LocalPointField (M.baseChange S L).toFF =
      IntermediateField.adjoin L (Set.range (W.pointFieldEmbedding L)) := by
  rw [← W.fixedField_restrictedPointActionKernel L, LocalPointField]
  congr 1
  ext σ
  rw [FF.mem_pointActionKernel, Subgroup.mem_comap,
    FiniteContinuousGaloisModule.mem_pointActionKernel]
  rfl

end ThreeAdicPlan.HasFiniteFlatModel

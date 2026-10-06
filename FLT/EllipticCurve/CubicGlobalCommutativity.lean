/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProductDensity

/-! # Commutativity of global cubic addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Spectrum identifies tensor-factor interchange with the symmetry of the scheme product. -/
@[reassoc] theorem pullbackSpecIso_symmetry
    (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
    (pullbackSpecIso R A B).inv ≫
      (pullbackSymmetry
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).hom ≫
      (pullbackSpecIso R B A).hom =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm R B A).toRingHom) := by
  apply (cancel_mono (pullbackSpecIso R B A).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSpecIso_inv_snd, pullbackSpecIso_inv_fst]
    rw [← Spec.map_comp]
    congr 1
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp]
    congr 1

/-- The descended addition is commutative on the full scheme product. -/
@[reassoc (attr := simp)] theorem addition_comm [W.IsElliptic] :
    (pullbackSymmetry (toBase W) (toBase W)).hom ≫ addition W = addition W := by
  apply affinePair_hom_ext W (toBase W)
  · simp only [Category.assoc, addition_toBase, pullbackSymmetry_hom_comp_fst_assoc]
    exact pullback.condition.symm
  · rw [chartPairInclusion_symmetry_assoc, addition_restrict_pair]
    apply (cancel_epi (pullbackSpecIso R (Ring W false) (Ring W false)).inv).mp
    simp only [chartAdditionMorphism, chartAddition, chartToBase,
      pullbackSpecIso_symmetry_assoc, Iso.inv_hom_id_assoc]
    exact affineAddition_comm W

/-- The graph of negation followed by the original point. -/
def leftInverseGraph : scheme W ⟶ pullback (toBase W) (toBase W) :=
  pullback.lift (negation W) (𝟙 _) (by simp)

@[reassoc] theorem leftInverseGraph_eq_swap :
    leftInverseGraph W =
      inverseGraph W ≫ (pullbackSymmetry (toBase W) (toBase W)).hom := by
  apply pullback.hom_ext <;> simp [leftInverseGraph, inverseGraph]

/-- Negation is also a left inverse everywhere. -/
@[reassoc (attr := simp)] theorem addition_inverse_left [W.IsElliptic] :
    leftInverseGraph W ≫ addition W = toBase W ≫ infinity W := by
  rw [leftInverseGraph_eq_swap, Category.assoc, addition_comm, addition_inverse_right]

end WeierstrassCurve.CubicCharts

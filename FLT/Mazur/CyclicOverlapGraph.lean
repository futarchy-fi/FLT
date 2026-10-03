/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicAtlas
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
/-!
# Closed graphs of the cyclic Laurent overlaps

The two node coordinates restrict to T and T⁻¹, so the map from the tensor
product of node rings onto the Laurent overlap ring is surjective.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct LaurentPolynomial
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.CyclicOverlapGraph
open PolygonNodeEqualizer PolygonNodeLocalization
variable (K : Type u) [Field K]
/-- Restriction from the first node chart. -/
def leftAlg : A (R := K) →ₐ[K] K[T;T⁻¹] :=
  ⟨leftMap, fun r ↦ Polynomial.toLaurent_C r⟩
/-- Restriction from the adjacent chart, with inverse coordinate. -/
def rightAlg : A (R := K) →ₐ[K] K[T;T⁻¹] :=
  LaurentPolynomial.invert.toAlgHom.comp ⟨rightMap, fun r ↦ Polynomial.toLaurent_C r⟩
/-- Ring map for the overlap graph in the product of node charts. -/
def graphMap : A (R := K) ⊗[K] A (R := K) →ₐ[K] K[T;T⁻¹] :=
  Algebra.TensorProduct.lift (leftAlg K) (rightAlg K) (fun _ _ ↦ Commute.all _ _)
/-- The two branch coordinates generate every Laurent polynomial. -/
theorem graphMap_surjective : Function.Surjective (graphMap K) := by
  intro p
  change p ∈ (graphMap K).range
  have hpos : LaurentPolynomial.T 1 ∈ (graphMap K).range := by
    refine ⟨x ⊗ₜ[K] 1, ?_⟩
    change graphMap K (x ⊗ₜ[K] 1) = _
    simp only [graphMap, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    exact leftMap_x
  have hneg : LaurentPolynomial.T (-1) ∈ (graphMap K).range := by
    refine ⟨1 ⊗ₜ[K] y, ?_⟩
    change graphMap K (1 ⊗ₜ[K] y) = _
    simp only [graphMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    change LaurentPolynomial.invert (rightMap y) = _
    rw [rightMap_y, LaurentPolynomial.invert_T]
  induction p using LaurentPolynomial.induction_on with
  | h_C a => exact (graphMap K).range.algebraMap_mem a
  | h_add hp hq => exact (graphMap K).range.add_mem hp hq
  | h_C_mul_T n a ha =>
    simpa only [mul_assoc, ← LaurentPolynomial.T_add] using (graphMap K).range.mul_mem ha hpos
  | h_C_mul_T_Z n a ha =>
    simpa only [mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg] using
      (graphMap K).range.mul_mem ha hneg
/-- The actual overlap graph in the product over the coefficient field. -/
def graph : ProjectiveLine.overlap K ⟶
    pullback (PolygonNodeBranches.toBase K) (PolygonNodeBranches.toBase K) :=
  pullback.lift (PolygonNodeBranches.left K)
    ((ProjectiveLine.inversion K).hom ≫ PolygonNodeBranches.right K)
    (by
      rw [Category.assoc, PolygonNodeBranches.right_toBase, PolygonNodeBranches.left_toBase]
      exact (PolygonCyclicAtlas.inversion_toBase K).symm)
/-- The overlap graph is the spectrum of the explicit tensor ring map. -/
theorem graph_eq_spec : graph K =
    Spec.map (CommRingCat.ofHom (graphMap K).toRingHom) ≫
      (pullbackSpecIso K (A (R := K)) (A (R := K))).inv := by
  apply pullback.hom_ext
  · erw [graph, pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change leftMap a = graphMap K (a ⊗ₜ[K] 1)
    simp [graphMap, leftAlg]
  · erw [graph, pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
      ProjectiveLine.inversion_hom, PolygonNodeBranches.right, ← Spec.map_comp,
      ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change LaurentPolynomial.invert (rightMap a) = graphMap K (1 ⊗ₜ[K] a)
    simp [graphMap, rightAlg]
/-- The cyclic overlap graph is a closed immersion. -/
instance graph_closed : IsClosedImmersion (graph K) := by
  rw [graph_eq_spec]
  let q : CommRingCat.of (A (R := K) ⊗[K] A (R := K)) ⟶
      CommRingCat.of K[T;T⁻¹] := CommRingCat.ofHom (graphMap K).toRingHom
  have hs : Function.Surjective q := by
    intro z
    obtain ⟨a, ha⟩ := graphMap_surjective K z
    exact ⟨a, ha⟩
  have : IsClosedImmersion (Spec.map q) := IsClosedImmersion.spec_of_surjective q hs
  exact inferInstanceAs (IsClosedImmersion (Spec.map q ≫
    (pullbackSpecIso K (A (R := K)) (A (R := K))).inv))
end FLT.Mazur.CyclicOverlapGraph

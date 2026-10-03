/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonGluing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
/-!
# Closed graph of the one-gon overlap

For z = t/(t-1), the expression z + z⁻¹ - 2 inverts t(t-1).
The node ring and Laurent chart therefore generate the entire puncture ring.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped TensorProduct LaurentPolynomial
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.OneGonOverlapGraph
open PolygonNodePresentation OneGonTransition
variable (K : Type u) [Field K]
/-- Restriction from the pinched node chart. -/
def leftAlg : B (R := K) →ₐ[K] puncture K :=
  (IsScalarTower.toAlgHom K K[X] (puncture K)).comp (B (R := K)).val
/-- Restriction from the torus in its Möbius coordinate. -/
def rightAlg : K[T;T⁻¹] →ₐ[K] puncture K :=
  ⟨overlapMap K, overlapMap_C K⟩
/-- The ring map of the one-gon overlap graph. -/
def graphMap : B (R := K) ⊗[K] K[T;T⁻¹] →ₐ[K] puncture K :=
  Algebra.TensorProduct.lift (leftAlg K) (rightAlg K) (fun _ _ ↦ Commute.all _ _)
/-- The Laurent coordinate supplies the inverse of the conductor. -/
theorem inverse_conductor :
    leftAlg K u * (rightAlg K (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) - 2)) = 1 := by
  have hi : overlapMap K (LaurentPolynomial.T (-1)) = (↑((mobius K)⁻¹) : puncture K) := by
    have he : (mobius K : puncture K) * overlapMap K (LaurentPolynomial.T (-1)) = 1 := by
      rw [← overlapMap_T K, ← map_mul, ← LaurentPolynomial.T_add]
      simp
    calc
      _ = (↑((mobius K)⁻¹) : puncture K) *
          ((mobius K : puncture K) * overlapMap K (LaurentPolynomial.T (-1))) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [he, mul_one]
  simp only [map_sub, map_add, map_ofNat]
  rw [show rightAlg K (LaurentPolynomial.T 1) = (mobius K : puncture K) from overlapMap_T K,
    show rightAlg K (LaurentPolynomial.T (-1)) = (↑((mobius K)⁻¹) : puncture K) from hi]
  have hu : leftAlg K u = (coordinate K : puncture K) * (difference K : puncture K) := by
    rw [coordinate_val, show (difference K : puncture K) =
      algebraMap K[X] (puncture K) (X - 1) from by simp]
    exact map_mul (algebraMap K[X] (puncture K)) X (X - 1)
  rw [hu]
  change _ * ((mobius K : puncture K) + (↑((mobius K)⁻¹) : puncture K) - 2) = 1
  have ht := Units.mul_inv (coordinate K)
  have hd := Units.mul_inv (difference K)
  change (coordinate K : puncture K) * (↑((coordinate K)⁻¹) : puncture K) = 1 at ht
  change (difference K : puncture K) * (↑((difference K)⁻¹) : puncture K) = 1 at hd
  simp only [mobius, Units.val_mul, mul_inv_rev, inv_inv]
  rw [difference_val] at hd ⊢
  linear_combination (coordinate K : puncture K) ^ 2 * hd +
    ((coordinate K : puncture K) - 1) ^ 2 * ht
/-- The two chart rings generate the puncture ring. -/
theorem graphMap_surjective : Function.Surjective (graphMap K) := by
  let := (bPunctureMap (R := K)).toAlgebra
  let := b_isLocalization (R := K)
  intro z
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (u (R := K)) z
  change z * (leftAlg K u) ^ n = leftAlg K b at hb
  let q : K[T;T⁻¹] := LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) - 2
  refine ⟨(b ⊗ₜ[K] 1) * (1 ⊗ₜ[K] q) ^ n, ?_⟩
  rw [map_mul, map_pow]
  simp only [graphMap, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
  rw [← hb]
  calc
    z * leftAlg K u ^ n * rightAlg K q ^ n = z * (leftAlg K u * rightAlg K q) ^ n := by ring
    _ = z := by rw [inverse_conductor]; simp
/-- The actual overlap graph in the product of the two affine charts. -/
def graph : Spec (.of (puncture K)) ⟶
    pullback (bToBase K) (OneGonGluing.torusToBase K) :=
  pullback.lift (bPuncture K) (toTorus K) (OneGonGluing.overlap_toBase K)
/-- Identify the graph with the spectrum of the tensor ring map. -/
theorem graph_eq_spec : graph K =
    Spec.map (CommRingCat.ofHom (graphMap K).toRingHom) ≫
      (pullbackSpecIso K (B (R := K)) K[T;T⁻¹]).inv := by
  apply pullback.hom_ext
  · erw [graph, pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change bPunctureMap b = graphMap K (b ⊗ₜ[K] 1)
    simp only [graphMap, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  · erw [graph, pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
      toTorus_eq_specMap, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change overlapMap K b = graphMap K (1 ⊗ₜ[K] b)
    simp only [graphMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
instance graph_closed : IsClosedImmersion (graph K) := by
  rw [graph_eq_spec]
  let q : CommRingCat.of (B (R := K) ⊗[K] K[T;T⁻¹]) ⟶
      CommRingCat.of (puncture K) := CommRingCat.ofHom (graphMap K).toRingHom
  have hs : Function.Surjective q := by
    intro z
    obtain ⟨a, ha⟩ := graphMap_surjective K z
    exact ⟨a, ha⟩
  have : IsClosedImmersion (Spec.map q) := IsClosedImmersion.spec_of_surjective q hs
  exact inferInstanceAs (IsClosedImmersion (Spec.map q ≫
    (pullbackSpecIso K (B (R := K)) K[T;T⁻¹]).inv))
end FLT.Mazur.OneGonOverlapGraph

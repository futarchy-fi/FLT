/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupOverlapCoordinates
public import FLT.Mazur.EllipticSubgroupClosureGluing
public import FLT.Mazur.PrincipalLocalizationGeneration
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed graph of the subgroup closure overlap

The two chart rings generate the overlap: the left ring supplies numerators
and the right chart's normalizing coordinate supplies the inverse denominator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- Restriction from the left closure chart to the overlap. -/
def closureOverlapLeftAlg : Closure A W H j →ₐ[A] LocalizedClosure A W H j k :=
  IsScalarTower.toAlgHom A _ _

/-- Restriction from the right closure chart, after changing coordinates. -/
def closureOverlapRightAlg : Closure A W H k →ₐ[A] LocalizedClosure A W H j k :=
  (localizedClosureEquiv A W H j k).toAlgHom.comp (IsScalarTower.toAlgHom A _ _)

/-- The algebra map defining the overlap graph. -/
def closureOverlapGraphMap :
    Closure A W H j ⊗[A] Closure A W H k →ₐ[A] LocalizedClosure A W H j k :=
  Algebra.TensorProduct.lift (closureOverlapLeftAlg A W H j k)
    (closureOverlapRightAlg A W H j k) (fun _ _ => Commute.all _ _)

/-- Both chart restrictions together generate the entire overlap algebra. -/
theorem closureOverlapGraphMap_surjective :
    Function.Surjective (closureOverlapGraphMap A W H j k) := by
  intro z
  obtain ⟨a, n, rfl⟩ := PrincipalLocalizationGeneration.fraction_representation
    (closureCoord A W H j k) z
  refine ⟨(a ⊗ₜ[A] 1) * (1 ⊗ₜ[A] closureCoord A W H k j) ^ n, ?_⟩
  simp only [map_mul, map_pow, closureOverlapGraphMap, Algebra.TensorProduct.lift_tmul,
    map_one, mul_one, one_mul]
  change algebraMap (Closure A W H j) (LocalizedClosure A W H j k) a *
    (localizedClosureEquiv A W H j k (algebraMap (Closure A W H k)
      (LocalizedClosure A W H k j) (closureCoord A W H k j))) ^ n = _
  rw [localizedClosureEquiv_normalizer]

/-- The overlap graph in the product of the two closure charts over the base. -/
def closureOverlapGraph : closureIntersection A W H j k ⟶
    pullback (closureChartToBase A W H j) (closureChartToBase A W H k) :=
  pullback.lift (closureToLeft A W H j k) (closureToRight A W H j k)
    (closure_overlap_toBase A W H j k)

set_option backward.isDefEq.respectTransparency false in
/-- The geometric graph is the spectrum of the surjective tensor algebra map. -/
theorem closureOverlapGraph_eq_spec : closureOverlapGraph A W H j k =
    Spec.map (CommRingCat.ofHom (closureOverlapGraphMap A W H j k).toRingHom) ≫
      (pullbackSpecIso A (Closure A W H j) (Closure A W H k)).inv := by
  apply pullback.hom_ext
  · erw [closureOverlapGraph, pullback.lift_fst, Category.assoc,
      pullbackSpecIso_inv_fst, closureToLeft, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change algebraMap (Closure A W H j) (LocalizedClosure A W H j k) a =
      closureOverlapGraphMap A W H j k (a ⊗ₜ[A] 1)
    simp only [closureOverlapGraphMap, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  · erw [closureOverlapGraph, pullback.lift_snd, Category.assoc,
      pullbackSpecIso_inv_snd]
    simp only [closureToRight, closureIntersectionIso, Functor.mapIso_hom, Iso.op_hom,
      RingEquiv.toCommRingCatIso_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
      closureToLeft, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change localizedClosureEquiv A W H j k
      (algebraMap (Closure A W H k) (LocalizedClosure A W H k j) a) =
        closureOverlapGraphMap A W H j k (1 ⊗ₜ[A] a)
    simp only [closureOverlapGraphMap, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual overlap has closed graph, without any finiteness assumption on the subgroup. -/
instance closureOverlapGraph_isClosedImmersion :
    IsClosedImmersion (closureOverlapGraph A W H j k) := by
  rw [closureOverlapGraph_eq_spec]
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (closureOverlapGraphMap A W H j k).toRingHom)
    (closureOverlapGraphMap_surjective A W H j k)
  infer_instance

end FLT.Mazur.EllipticSubgroupChart

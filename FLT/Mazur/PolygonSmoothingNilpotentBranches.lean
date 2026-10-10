/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchOpens

/-!
# Disjoint branch opens at every nilpotent thickening

The full branch intersection D(t) is empty for nilpotent t, over any coefficient
ring. Inversion supplies the edge coordinate used between consecutive charts.
These statements do not assert disjointness over a nonnilpotent parameter.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial

namespace FLT.Mazur.PolygonSmoothing

variable (R : Type*) [CommRing R]

/-- Nilpotent smoothing parameters make the actual two branch opens disjoint. -/
theorem branchOpen_nilpotent_disjoint (t : R) (ht : IsNilpotent t) :
    Disjoint (Set.range (leftBranchOpen R t)) (Set.range (rightBranchOpen R t)) := by
  rw [Set.disjoint_iff_inter_eq_empty, branchOpen_intersection]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨m, hm⟩ := ht
  apply hz
  apply z.isPrime.mem_of_pow_mem m
  rw [← map_pow, hm, map_zero]
  exact z.asIdeal.zero_mem

/-- Inversion on the arithmetic edge torus, over an arbitrary coefficient ring. -/
def edgeInversion : branchTorus R ≅ branchTorus R :=
  Scheme.Spec.mapIso (LaurentPolynomial.invert.toRingEquiv.toCommRingCatIso.op)

/-- Arithmetic edge inversion preserves the coefficient morphism. -/
@[reassoc] theorem edgeInversion_base :
    (edgeInversion R).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) =
      Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp

/-- The edge enters the preceding node chart in the inverse right coordinate. -/
def precedingBranch (t : R) : branchTorus R ⟶ chart R t :=
  (edgeInversion R).hom ≫ rightBranchOpen R t

instance precedingBranch_isOpenImmersion (t : R) : IsOpenImmersion (precedingBranch R t) := by
  unfold precedingBranch
  infer_instance

/-- The inverse-coordinate edge retains the arithmetic base. -/
@[reassoc] theorem precedingBranch_base (t : R) :
    precedingBranch R t ≫ chartStructure R t =
      Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) := by
  rw [precedingBranch, Category.assoc, rightBranchOpen_base, edgeInversion_base]

/-- Inversion does not shrink the original right branch open. -/
theorem precedingBranch_range (t : R) :
    Set.range (precedingBranch R t) = Set.range (rightBranchOpen R t) := by
  change Set.range ((rightBranchOpen R t) ∘ (edgeInversion R).hom) = _
  exact (edgeInversion R).hom.homeomorph.surjective.range_comp _

/-- The cyclic incoming and outgoing edges are disjoint at a nilpotent thickening. -/
theorem cyclicBranch_disjoint (t : R) (ht : IsNilpotent t) :
    Disjoint (Set.range (leftBranchOpen R t)) (Set.range (precedingBranch R t)) := by
  rw [precedingBranch_range]
  exact branchOpen_nilpotent_disjoint R t ht

end FLT.Mazur.PolygonSmoothing

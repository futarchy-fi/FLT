/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentBranches
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Closed arithmetic edge graphs

The outgoing coordinate of one chart and the incoming coordinate of the next
restrict to z and z⁻¹. They generate the Laurent algebra, so the actual edge
map to the product of charts is a closed immersion over any coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct LaurentPolynomial

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R] (t : R)

/-- Restriction to the incoming arithmetic edge with its inverse coordinate. -/
def precedingLaurentMap : ChartRing t →ₐ[R] R[T;T⁻¹] :=
  LaurentPolynomial.invert.toAlgHom.comp ((leftLaurentMap t).comp (branchSwapMap t))

/-- The original incoming coordinate becomes the inverse edge variable. -/
@[simp] theorem precedingLaurentMap_right :
    precedingLaurentMap R t (rightCoordinate t) = LaurentPolynomial.T (-1) := by
  simp [precedingLaurentMap]

/-- The actual outgoing branch is the spectrum of its Laurent restriction. -/
theorem leftBranchOpen_eq_spec : leftBranchOpen R t =
    Spec.map (CommRingCat.ofHom (leftLaurentMap t).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact leftPunctureToLaurent_map t

/-- The actual incoming branch is the spectrum of its inverse Laurent restriction. -/
theorem precedingBranch_eq_spec : precedingBranch R t =
    Spec.map (CommRingCat.ofHom (precedingLaurentMap R t).toRingHom) := by
  change Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change LaurentPolynomial.invert (leftPunctureToLaurent t
    (rightToLeftPuncture t (algebraMap (ChartRing t) _ a))) = _
  rw [rightToLeftPuncture_map, leftPunctureToLaurent_map]
  rfl

/-- The explicit tensor algebra map defining the full edge graph. -/
def edgeGraphMap : ChartRing t ⊗[R] ChartRing t →ₐ[R] R[T;T⁻¹] :=
  Algebra.TensorProduct.lift (leftLaurentMap t) (precedingLaurentMap R t)
    (fun _ _ ↦ Commute.all _ _)

/-- The outgoing and incoming coordinates generate the entire edge algebra. -/
theorem edgeGraphMap_surjective : Function.Surjective (edgeGraphMap R t) := by
  intro p
  change p ∈ (edgeGraphMap R t).range
  have hpos : LaurentPolynomial.T 1 ∈ (edgeGraphMap R t).range := by
    refine ⟨leftCoordinate t ⊗ₜ[R] 1, ?_⟩
    simp [edgeGraphMap]
  have hneg : LaurentPolynomial.T (-1) ∈ (edgeGraphMap R t).range := by
    refine ⟨1 ⊗ₜ[R] rightCoordinate t, ?_⟩
    simp [edgeGraphMap]
  induction p using LaurentPolynomial.induction_on with
  | h_C a => exact (edgeGraphMap R t).range.algebraMap_mem a
  | h_add hp hq => exact (edgeGraphMap R t).range.add_mem hp hq
  | h_C_mul_T n a ha =>
    simpa only [mul_assoc, ← LaurentPolynomial.T_add] using
      (edgeGraphMap R t).range.mul_mem ha hpos
  | h_C_mul_T_Z n a ha =>
    simpa only [mul_assoc, ← LaurentPolynomial.T_add, sub_eq_add_neg] using
      (edgeGraphMap R t).range.mul_mem ha hneg

/-- The actual arithmetic edge graph in the product of consecutive charts. -/
def edgeGraph : branchTorus R ⟶ pullback (chartStructure R t) (chartStructure R t) :=
  pullback.lift (leftBranchOpen R t) (precedingBranch R t)
    ((leftBranchOpen_base R t).trans (precedingBranch_base R t).symm)

/-- The edge graph is the spectrum of the explicit surjective tensor map. -/
theorem edgeGraph_eq_spec : edgeGraph R t =
    Spec.map (CommRingCat.ofHom (edgeGraphMap R t).toRingHom) ≫
      (pullbackSpecIso R (ChartRing t) (ChartRing t)).inv := by
  apply pullback.hom_ext
  · erw [edgeGraph, pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst,
      leftBranchOpen_eq_spec, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change leftLaurentMap t a = edgeGraphMap R t (a ⊗ₜ[R] 1)
    simp [edgeGraphMap]
  · erw [edgeGraph, pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
      precedingBranch_eq_spec, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change precedingLaurentMap R t a = edgeGraphMap R t (1 ⊗ₜ[R] a)
    simp [edgeGraphMap]

attribute [local irreducible] edgeGraphMap

/-- Each full arithmetic edge graph is a closed immersion. -/
instance edgeGraph_closed : IsClosedImmersion (edgeGraph R t) := by
  rw [edgeGraph_eq_spec]
  let q : CommRingCat.of (ChartRing t ⊗[R] ChartRing t) ⟶ CommRingCat.of R[T;T⁻¹] :=
    CommRingCat.ofHom (edgeGraphMap R t).toRingHom
  let _ : IsClosedImmersion (Spec.map q) :=
    IsClosedImmersion.spec_of_surjective q (edgeGraphMap_surjective R t)
  exact inferInstanceAs (IsClosedImmersion (Spec.map q ≫
    (pullbackSpecIso R (ChartRing t) (ChartRing t)).inv))

end FLT.Mazur.PolygonSmoothing

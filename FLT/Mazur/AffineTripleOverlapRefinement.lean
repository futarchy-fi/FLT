/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTripleOverlapMaps

/-!
# Refinement maps on affine triple tensor rings

A commutative ring square induces maps of double and triple tensor rings.
The triple map commutes with all three coordinate inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
universe u
namespace FLT.Mazur.AffineTripleOverlapRefinement
open AffineOverlapTensor AffineTripleOverlapMaps
variable {R S R' S' : Type u}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R' S']
variable (a : R →+* R') (b : S →+* S')
variable (w : b.comp (algebraMap R S) = (algebraMap R' S').comp a)

/-- The ring map on double overlaps induced by the square. -/
def doubleMap : S ⊗[R] S →+* S' ⊗[R'] S' :=
  Algebra.TensorProduct.mapRingHom a b b w w

/-- Refinement on a pure double tensor. -/
@[simp]
theorem doubleMap_tmul (s t : S) :
    doubleMap a b w (s ⊗ₜ[R] t) = b s ⊗ₜ[R'] b t :=
  Algebra.TensorProduct.mapRingHom_tmul a b b w w s t

/-- The double-overlap map respects the base-ring square. -/
theorem doubleMap_algebraMap :
    (doubleMap a b w).comp (algebraMap R (S ⊗[R] S)) =
      (algebraMap R' (S' ⊗[R'] S')).comp a := by
  ext r
  simp only [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, doubleMap_tmul,
    map_one]
  exact congrArg (fun s : S' ↦ s ⊗ₜ[R'] (1 : S')) (RingHom.congr_fun w r)

/-- The ring map on triple overlaps induced by the square. -/
def tripleMap : Triple R S →+* Triple R' S' :=
  Algebra.TensorProduct.mapRingHom a b (doubleMap a b w) w (doubleMap_algebraMap a b w)

/-- Refinement on a pure triple tensor. -/
@[simp]
theorem tripleMap_tmul (s t v : S) :
    tripleMap a b w (s ⊗ₜ[R] (t ⊗ₜ[R] v)) = b s ⊗ₜ[R'] (b t ⊗ₜ[R'] b v) := by
  simp [tripleMap]

/-- The first coordinate commutes with refinement. -/
theorem tripleMap_coord1 :
    (tripleMap a b w).comp (coord1 R S) = (coord1 R' S').comp b :=
  Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom ..

/-- The second coordinate commutes with refinement. -/
theorem tripleMap_coord2 :
    (tripleMap a b w).comp (coord2 R S) = (coord2 R' S').comp b := by
  ext s
  change tripleMap a b w (1 ⊗ₜ[R] (s ⊗ₜ[R] 1)) = 1 ⊗ₜ[R'] (b s ⊗ₜ[R'] 1)
  simp

/-- The third coordinate commutes with refinement. -/
theorem tripleMap_coord3 :
    (tripleMap a b w).comp (coord3 R S) = (coord3 R' S').comp b := by
  ext s
  change tripleMap a b w (1 ⊗ₜ[R] (1 ⊗ₜ[R] s)) = 1 ⊗ₜ[R'] (1 ⊗ₜ[R'] b s)
  simp

end FLT.Mazur.AffineTripleOverlapRefinement

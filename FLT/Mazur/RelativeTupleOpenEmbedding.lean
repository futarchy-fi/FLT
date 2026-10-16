/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFiniteTupleAffine

/-!
# Open embeddings on finite relative tuple schemes

An open embedding over the unchanged base induces an open embedding of full
finite tuple schemes. This transports an affine envelope to all finite powers
without replacing the original source by an affine branch.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {E F : Over S} (j : E ⟶ F)

/-- Apply the original map to every coordinate. -/
def tupleMap (I : Type) [Fintype I] : tuples E I ⟶ tuples F I :=
  lift F I fun i ↦ coordinate E I i ≫ j

/-- The induced map retains every original coordinate. -/
@[reassoc (attr := simp)] theorem tupleMap_coordinate (I : Type) [Fintype I] (i : I) :
    tupleMap j I ≫ coordinate F I i = coordinate E I i ≫ j := lift_coordinate F I _ i

/-- Splitting the first label intertwines tuple maps with relative binary product maps. -/
@[reassoc] theorem tupleMap_finSuccIso (n : ℕ) :
    tupleMap j (Fin (n + 1)) ≫ (finSuccIso F n).hom =
      (finSuccIso E n).hom ≫ prod.map j (tupleMap j (Fin n)) := by
  apply prod.hom_ext
  · simp [finSuccIso, tupleMap, coordinate, lift]
  · apply hom_ext
    intro i
    simp [finSuccIso, tupleMap, coordinate, lift]

/-- Products of two open embeddings over a base are open embeddings. -/
theorem binaryMap_open {A B C D : Over S} (a : A ⟶ B) (b : C ⟶ D)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] :
    IsOpenImmersion (prod.map a b).left := by
  let _ : IsOpenImmersion (prod.map a (𝟙 C)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_prod_fst_with_id a C).map (Over.forget S))
      (inferInstanceAs (IsOpenImmersion a.left))
  let _ : IsOpenImmersion (prod.map b (𝟙 B)).left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_prod_fst_with_id b B).map (Over.forget S))
      (inferInstanceAs (IsOpenImmersion b.left))
  let _ : IsOpenImmersion (prod.map (𝟙 B) b).left := by
    have h : prod.map (𝟙 B) b =
        (prod.braiding B C).hom ≫ prod.map b (𝟙 B) ≫ (prod.braiding D B).hom := by
      apply prod.hom_ext <;> simp
    rw [h, Over.comp_left, Over.comp_left]
    infer_instance
  have h : prod.map a b = prod.map a (𝟙 C) ≫ prod.map (𝟙 B) b := by
    simp
  rw [h, Over.comp_left]
  infer_instance

/-- The complete finite tuple map is open whenever the original map is open. -/
theorem finTupleMap_open [IsOpenImmersion j.left] (n : ℕ) :
    IsOpenImmersion (tupleMap j (Fin n)).left := by
  induction n with
  | zero =>
    have h : tupleMap j (Fin 0) = (finZeroIso E).hom ≫ (finZeroIso F).inv := by
      apply hom_ext
      intro i
      exact Fin.elim0 i
    rw [h, Over.comp_left]
    infer_instance
  | succ n ih =>
    let _ := ih
    let _ := binaryMap_open j (tupleMap j (Fin n))
    have h : tupleMap j (Fin (n + 1)) = (finSuccIso E n).hom ≫
        prod.map j (tupleMap j (Fin n)) ≫ (finSuccIso F n).inv := by
      rw [← tupleMap_finSuccIso_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h, Over.comp_left, Over.comp_left]
    infer_instance

end FLT.Mazur.RelativeOrderedTuples

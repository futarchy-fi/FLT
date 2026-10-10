/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementFamily
public import FLT.Mazur.SchemeAffineCommonBaseCover
/-!
# Constructing simultaneous refinements for affine triple tests

Two successive faithfully flat common covers retain all three independent covering maps.
The construction applies to arbitrary affine tests with a common map into the base scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X}
variable (C : Fin 3 → Chart p) {A : CommRingCat.{u}} (a : Spec A ⟶ X)
variable (f : ∀ i, (C i).baseRing ⟶ A) (w : ∀ i, Spec.map (f i) ≫ (C i).base = a)

/-- Common covering ring for the first two affine charts. -/
def tripleFirstPair : (C 0).CrossRefinement (C 1) :=
  (C 0).commonBaseCrossRefinement (C 1) (f 0) (f 1) ((w 0).trans (w 1).symm)

/-- A second faithfully flat common cover includes the third chart. -/
def tripleLastPair : (tripleFirstPair C a f w).leftChart.CrossRefinement (C 2) :=
  (tripleFirstPair C a f w).leftChart.commonBaseCrossRefinement (C 2) (𝟙 _) (f 2) (by
    change Spec.map (𝟙 A) ≫ (Spec.map (f 0) ≫ (C 0).base) = _
    rw [Spec.map_id, Category.id_comp]
    exact (w 0).trans (w 2).symm)

/-- The first original covering map factors through the iterated common cover. -/
theorem tripleCoverLeft_square :
    (C 0).ringMap ≫ ((tripleFirstPair C a f w).leftCover ≫
        (tripleLastPair C a f w).leftCover) =
      f 0 ≫ (tripleLastPair C a f w).ringMap := by
  rw [← Category.assoc, (tripleFirstPair C a f w).leftSquare, Category.assoc]
  have h := (tripleLastPair C a f w).leftSquare
  change (tripleFirstPair C a f w).ringMap ≫ _ = (𝟙 A) ≫ _ at h
  rw [Category.id_comp] at h
  rw [h]
  rfl

/-- The second original covering map factors independently through the common cover. -/
theorem tripleCoverMiddle_square :
    (C 1).ringMap ≫ ((tripleFirstPair C a f w).rightCover ≫
        (tripleLastPair C a f w).leftCover) =
      f 1 ≫ (tripleLastPair C a f w).ringMap := by
  rw [← Category.assoc, (tripleFirstPair C a f w).rightSquare, Category.assoc]
  have h := (tripleLastPair C a f w).leftSquare
  change (tripleFirstPair C a f w).ringMap ≫ _ = (𝟙 A) ≫ _ at h
  rw [Category.id_comp] at h
  rw [h]
  rfl

/-- Construct simultaneous refinements for any three charts over a common affine base. -/
def tripleCrossRefinementFamily : CrossRefinementFamily C where
  baseRing := A
  coverRing := (tripleLastPair C a f w).coverRing
  ringMap := (tripleLastPair C a f w).ringMap
  faithfullyFlat := (tripleLastPair C a f w).faithfullyFlat
  base := a
  baseMap := f
  coverMap := Fin.cases
    ((tripleFirstPair C a f w).leftCover ≫ (tripleLastPair C a f w).leftCover)
    (Fin.cases
      ((tripleFirstPair C a f w).rightCover ≫ (tripleLastPair C a f w).leftCover)
      (Fin.cases (tripleLastPair C a f w).rightCover (fun i ↦ i.elim0)))
  square := by
    intro i
    fin_cases i
    · exact tripleCoverLeft_square C a f w
    · exact tripleCoverMiddle_square C a f w
    · exact (tripleLastPair C a f w).rightSquare
  base_over := w

/-- An actual affine triple test supplies the required simultaneous refinement family. -/
def tripleCrossRefinementFamilyOfMaps (b : ∀ i, Spec A ⟶ Spec (C i).baseRing)
    (h : ∀ i, b i ≫ (C i).base = a) : CrossRefinementFamily C :=
  tripleCrossRefinementFamily C a (fun i ↦ Spec.preimage (b i))
    (fun i ↦ by simpa only [Spec.map_preimage] using h i)

/-- The constructed family has exactly the coordinates of the given geometric test. -/
theorem tripleCrossRefinementFamilyOfMaps_baseMap
    (b : ∀ i, Spec A ⟶ Spec (C i).baseRing) (h : ∀ i, b i ≫ (C i).base = a) (i : Fin 3) :
    Spec.map ((tripleCrossRefinementFamilyOfMaps C a b h).baseMap i) = b i :=
  Spec.map_preimage (b i)

end FLT.Mazur.SchemeAffineDescent.Chart

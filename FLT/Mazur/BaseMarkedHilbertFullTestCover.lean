/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullTestPullback
public import FLT.Mazur.BaseMarkedHilbertFullRelation

/-!
# Actual covers of the full relation by original mixed chart intersections

An original test cover pulls back to the full intersections. Refining by the
Hilbert chart cover gives actual original full intersections on both ends.
Specializing to the glued test proves coverage of its full relation scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
  {U : Over (Spec (.of R))} (s : (relativeFppfSheaf f).obj.obj (op U))
  {κ : Type} (W : κ → Over (Spec (.of R))) (b : ∀ j, W j ⟶ U)
  (hb : ∀ x : U.left, ∃ j, ∃ y : (W j).left, (b j).left y = x)
local notation "sW" j => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op (b j)) s

include hb in
/-- Original covering test maps give a jointly surjective family of full intersections. -/
theorem baseMarkedFullTestChanges_cover (x : (baseMarkedFullIntersection f V a U s).left) :
    ∃ j, ∃ y : (baseMarkedFullIntersection f V a (W j) (sW j)).left,
      (baseMarkedFullTestChange f hL V a (b j) s).left y = x := by
  obtain ⟨j, y, hy⟩ := hb ((baseMarkedFullToTest f V a U s).left x)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    ((baseMarkedFullTestChange_isPullback f hL V a (b j) s).map (Over.forget _)) x y hy.symm
  exact ⟨j, z, hz⟩

/-- The actual full intersections form an open cover when the original test maps do. -/
def baseMarkedFullTestCover [∀ j, IsOpenImmersion (b j).left] :
    (baseMarkedFullIntersection f V a U s).left.OpenCover where
  I₀ := κ
  X j := (baseMarkedFullIntersection f V a (W j) (sW j)).left
  f j := (baseMarkedFullTestChange f hL V a (b j) s).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨baseMarkedFullTestChanges_cover f hL V a s W b hb, fun j ↦ inferInstance⟩

/-- Refining by actual Hilbert charts gives a cover by the ORIGINAL full intersections. -/
def baseMarkedFullMixedCover [∀ j, IsOpenImmersion (b j).left] :
    (baseMarkedFullIntersection f V a U s).left.OpenCover where
  I₀ := κ × ι
  X ji := (variableHilbertOverlap f (a ji.2).1 V (a ji.2).2 (W ji.1) (sW ji.1)).left
  f ji := (baseMarkedFullChart f V a (W ji.1) (sW ji.1) ji.2 ≫
    baseMarkedFullTestChange f hL V a (b ji.1) s).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨j, y, hy⟩ := baseMarkedFullTestChanges_cover f hL V a s W b hb x
      obtain ⟨i, z, hz⟩ := (baseMarkedFullCover f V a (W j) (sW j)).exists_eq y
      refine ⟨(j, i), z, ?_⟩
      change (baseMarkedFullTestChange f hL V a (b j) s).left
        ((baseMarkedFullChart f V a (W j) (sW j) i).left z) = x
      exact (congrArg (baseMarkedFullTestChange f hL V a (b j) s).left hz).trans hy
    · intro ji
      have : IsOpenImmersion (baseMarkedFullChart f V a (W ji.1) (sW ji.1) ji.2).left :=
        (baseMarkedFullCover f V a (W ji.1) (sW ji.1)).map_prop ji.2
      change IsOpenImmersion ((baseMarkedFullChart f V a (W ji.1) (sW ji.1) ji.2).left ≫
        (baseMarkedFullTestChange f hL V a (b ji.1) s).left)
      infer_instance

/-- The full relation scheme is covered by original full mixed Hilbert-chart intersections. -/
def baseMarkedFullRelationCover : (baseMarkedFullRelation f hL V a).left.OpenCover :=
  baseMarkedFullMixedCover f hL V a (baseMarkedGluedPicard f hL V a)
    (fun j ↦ variableHilbertTest f (a j).1 V) (baseMarkedGluedArrow f hL V a)
    (fun x ↦ (baseMarkedGluedCover f hL V a).exists_eq x)

/-- The sections in this cover are precisely the original chart sections. -/
theorem baseMarkedFullRelationCover_section (j : ι) :
    (relativeFppfSheaf f).obj.map (baseMarkedGluedArrow f hL V a j).op
      (baseMarkedGluedPicard f hL V a) = baseMarkedChartSection f hL V (a j) :=
  baseMarkedGluedPicard_chart f hL V a j

end FLT.Mazur.HilbertChart

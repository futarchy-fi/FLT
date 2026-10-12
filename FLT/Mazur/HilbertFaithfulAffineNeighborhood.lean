/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleFaithfulSource
public import FLT.Mazur.AffineEtaleFaithfulCoefficients
public import FLT.Mazur.OrderedHilbertAffineEtaleTestCover

/-!
# Faithful-base affine neighborhoods in original full Hilbert intersections

Every point of a full chart intersection has an affine open neighborhood over
a constructed faithful translation base. The original intersection, test map,
translation coordinate and coefficient-base map are all retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve AffineEtaleFaithfulNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
local notation "I" => variableHilbertOverlap f d V c T s

/-- The translation coordinate of the original full chart intersection. -/
def faithfulOverlapCoordinate : I ⟶ V :=
  variableHilbertOverlapToChart f d hL V c T s ≫ variableHilbertBase f d V

omit [IsAffine V.left] in
/-- Every actual overlap point has an affine neighborhood over a constructed faithful base. -/
theorem exists_faithful_affine_overlap_neighborhood (y : (I).left) :
    ∃ (v : V.left) (A : Scheme) (j : A ⟶ (I).left)
      (β : A ⟶ (sourceOpen V.hom v).toScheme) (a : A),
      IsAffine A ∧ IsOpenImmersion j ∧ j a = y ∧
      β ≫ (sourceOpen V.hom v).ι = j ≫ (faithfulOverlapCoordinate f hL d V c T s).left ∧
      (β ≫ spectrumMap V.hom v) ≫ spectrumBase V.hom v = j ≫ (I).hom := by
  let C := (I).left.affineOpenCover
  obtain ⟨a, ha⟩ := C.covers y
  let z := C.idx y
  let γ := C.f z ≫ (faithfulOverlapCoordinate f hL d V c T s).left
  let v := γ a
  let A := (parameterOpen V.hom γ v).toScheme
  let j : A ⟶ (I).left := (parameterOpen V.hom γ v).ι ≫ C.f z
  let β : A ⟶ (sourceOpen V.hom v).toScheme := parameterMap V.hom γ v
  let a' : A := parameterPoint V.hom γ a
  have hj : j a' = y := ha
  have hβ : β ≫ (sourceOpen V.hom v).ι =
      j ≫ (faithfulOverlapCoordinate f hL d V c T s).left := by
    simpa only [j, γ, Category.assoc] using parameterMap_ι V.hom γ v
  refine ⟨v, A, j, β, a', inferInstance, inferInstance, hj, hβ, ?_⟩
  rw [Category.assoc, spectrumMap_base, ← Category.assoc, hβ, Category.assoc, Over.w]

end FLT.Mazur.HilbertChart

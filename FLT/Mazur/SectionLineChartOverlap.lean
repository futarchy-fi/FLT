/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSectionLineChart

/-!
# Section-line compatibility on intersections of coordinate charts

The two normalized generators of the same submodule differ by a constructed
unit, whose inverse is the opposite coordinate ratio. Consequently the actual
projective scheme morphism attached to that submodule is independent of the
coordinate used to trivialize it.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.NormalizedSectionLine
variable (S : Type u) [CommRing S] (ι : Type u)

/-- Generators of the same submodule differ by their actual coordinate ratio. -/
lemma generator_change (i j : ι) (L : Chart S ι i) (M : Chart S ι j)
    (h : L.val = M.val) :
    generator S ι i L = (generator S ι i L j) • generator S ι j M := by
  exact eq_smul_generator S ι j M
    ⟨generator S ι i L, h ▸ generator_mem S ι i L⟩

/-- The two coordinate ratios on a section-line overlap are mutual inverses. -/
lemma generator_ratio_mul (i j : ι) (L : Chart S ι i) (M : Chart S ι j)
    (h : L.val = M.val) :
    generator S ι i L j * generator S ι j M i = 1 := by
  have he := congrFun (generator_change S ι i j L M h) i
  simpa only [generator_coordinate, Pi.smul_apply, smul_eq_mul] using he.symm

/-- The overlap transition is a genuine unit constructed from the two generators. -/
def transitionUnit (i j : ι) (L : Chart S ι i) (M : Chart S ι j)
    (h : L.val = M.val) : Sˣ where
  val := generator S ι i L j
  inv := generator S ι j M i
  val_inv := generator_ratio_mul S ι i j L M h
  inv_val := generator_ratio_mul S ι j i M L h.symm

/-- Trivializing a section line in either chart gives the same projective scheme point. -/
lemma projectivePoint_change {R : Type u} [CommRing R] (f : R →+* S)
    (i j : ι) (L : Chart S ι i) (M : Chart S ι j) (h : L.val = M.val) :
    ProjectiveSpace.sectionLinePoint R ι f i L =
      ProjectiveSpace.sectionLinePoint R ι f j M := by
  rw [ProjectiveSpace.sectionLinePoint_eq_unitChartPoint,
    ProjectiveSpace.sectionLinePoint_eq_unitChartPoint]
  let a := transitionUnit S ι i j L M h
  have hx : generator S ι i L = fun k ↦ (a : S) * generator S ι j M k :=
    generator_change S ι i j L M h
  trans ProjectiveSpace.unitChartPoint R ι f (generator S ι i L) j a rfl
  · exact ProjectiveSpace.unitChartPoint_change R ι f _ i j 1 a
      (generator_coordinate S ι i L) rfl
  · have hs := ProjectiveSpace.unitChartPoint_scale R ι f (generator S ι j M) j 1 a
      (generator_coordinate S ι j M)
    simpa only [mul_one, ← hx] using hs

end FLT.Mazur.NormalizedSectionLine

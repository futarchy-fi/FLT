/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalFamily
public import FLT.Mazur.PolygonSmoothingMarkedSection

/-!
# Disjoint global sections of the infinitesimal cyclic family

A unit coordinate in each node chart gives an actual section of the assembled
family. Sections chosen in distinct charts have disjoint images, by the full
cyclic intersection relation and nilpotence of the smoothing parameter.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing

variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- The global marking specified by an actual chart unit and a cyclic node index. -/
def marking (i : Fin n) (a : Rˣ) : Spec (.of R) ⟶ scheme R t n h :=
  markedSection t a ≫ chart R t n h i

/-- Every global marking is a section over the original arithmetic base. -/
@[reassoc (attr := simp)] theorem marking_base (i : Fin n) (a : Rˣ) :
    marking R t n h i a ≫ toBase R t n h = 𝟙 _ := by
  rw [marking, Category.assoc, chart_toBase, markedSection_base]

omit [Fact (IsNilpotent t)] in
/-- The point of a local unit marking is contained in the original left branch. -/
theorem markedSection_mem_left (a : Rˣ) (x : Spec (.of R)) :
    markedSection t a x ∈ Set.range (leftBranchOpen R t) := by
  refine ⟨markedTorusSection a x, ?_⟩
  exact congrArg (fun f ↦ f x) (markedTorusSection_left t a)

/-- No point of a local unit marking lies in the incoming cyclic branch. -/
theorem markedSection_not_mem_preceding (a : Rˣ) (x : Spec (.of R)) :
    markedSection t a x ∉ Set.range (precedingBranch R t) := by
  exact Set.disjoint_left.mp (cyclicBranch_disjoint R t (Fact.out : IsNilpotent t))
    (markedSection_mem_left R t a x)

/-- Markings on distinct cyclic components have disjoint images in the glued family. -/
theorem markings_disjoint {i j : Fin n} (hij : i ≠ j) (a b : Rˣ) :
    Disjoint (Set.range (marking R t n h i a)) (Set.range (marking R t n h j b)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, he⟩
  have he' : chart R t n h i (markedSection t a x) =
      chart R t n h j (markedSection t b y) := he.symm
  rcases (charts_eq_iff R t n h hij _ _).mp he' with
    ⟨w, _, _, hw⟩ | ⟨w, _, hw, _⟩
  · exact markedSection_not_mem_preceding R t b y ⟨w, hw⟩
  · exact markedSection_not_mem_preceding R t a x ⟨w, hw⟩

/-- Any chosen unit on each chart gives pairwise disjoint global markings. -/
theorem pairwise_markings (a : Fin n → Rˣ) :
    Pairwise (fun i j ↦ Disjoint (Set.range (marking R t n h i (a i)))
      (Set.range (marking R t n h j (a j)))) := by
  intro i j hij
  exact markings_disjoint R t n h hij (a i) (a j)

/-- A marking lies in a smooth open subfamily of the assembled infinitesimal polygon. -/
instance marking_open_smooth (i : Fin n) :
    Smooth ((leftBranchOpen R t ≫ chart R t n h i) ≫ toBase R t n h) := by
  rw [Category.assoc, chart_toBase]
  infer_instance

end FLT.Mazur.PolygonInfinitesimal

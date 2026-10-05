/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# The finite intersection diagram of an affine cover

Nonempty finite sets of chart labels index the actual intersection opens.
Inclusions of label sets give open restriction maps in the reverse direction;
unions give the overlap pullbacks. For a finite affine cover of a separated
scheme this is a finite diagram of affine schemes, including repeated charts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

/-- Nonempty finite sets of chart labels; the empty intersection is excluded. -/
abbrev NonemptyChartSet (ι : Type v) := {s : Finset ι // s.Nonempty}

instance nonemptyChartSetFintype (ι : Type v) [Finite ι] : Fintype (NonemptyChartSet ι) :=
  Fintype.ofFinite _

variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)

/-- The actual open intersection of a nonempty finite set of charts. -/
def finiteIntersectionOpen (s : NonemptyChartSet ι) : X.Opens := ⨅ i ∈ s.val, U i

/-- Adding chart labels shrinks the intersection open. -/
theorem finiteIntersectionOpen_antitone : Antitone (finiteIntersectionOpen U) := by
  intro s t h
  apply le_iInf₂
  intro i hi
  exact iInf_le_of_le i (iInf_le _ (h hi))

/-- A single chart is one of the intersection objects. -/
def singletonChartSet (i : ι) : NonemptyChartSet ι := ⟨{i}, Finset.singleton_nonempty i⟩

/-- The singleton intersection is the original chart. -/
@[simp]
theorem finiteIntersectionOpen_singleton (i : ι) :
    finiteIntersectionOpen U (singletonChartSet i) = U i := by
  simp [finiteIntersectionOpen, singletonChartSet]

/-- The union of two nonempty sets of chart labels. -/
def unionChartSet (s t : NonemptyChartSet ι) : NonemptyChartSet ι := by
  classical
  exact ⟨s.val ∪ t.val, s.property.mono Finset.subset_union_left⟩

/-- The first set of labels is contained in its union. -/
theorem le_unionChartSet_left (s t : NonemptyChartSet ι) : s ≤ unionChartSet s t := by
  classical
  exact Finset.subset_union_left

/-- The second set of labels is contained in its union. -/
theorem le_unionChartSet_right (s t : NonemptyChartSet ι) : t ≤ unionChartSet s t := by
  classical
  exact Finset.subset_union_right

/-- Union of labels is intersection of the actual chart opens. -/
@[simp]
theorem finiteIntersectionOpen_union (s t : NonemptyChartSet ι) :
    finiteIntersectionOpen U (unionChartSet s t) =
      finiteIntersectionOpen U s ⊓ finiteIntersectionOpen U t := by
  classical
  simp only [finiteIntersectionOpen, unionChartSet, Finset.mem_union, iInf_or, iInf_inf_eq]

/-- The contravariant diagram of actual intersection opens. -/
def finiteIntersectionOpenDiagram : (NonemptyChartSet ι)ᵒᵖ ⥤ X.Opens where
  obj s := finiteIntersectionOpen U s.unop
  map f := homOfLE (finiteIntersectionOpen_antitone U (leOfHom f.unop))

/-- Restriction realizes the intersection diagram as actual open subschemes. -/
def finiteIntersectionSchemeDiagram : (NonemptyChartSet ι)ᵒᵖ ⥤ Scheme.{u} :=
  finiteIntersectionOpenDiagram U ⋙ X.restrictFunctor ⋙ Over.forget X

/-- Every arrow of the intersection diagram is an open immersion. -/
instance finiteIntersectionSchemeDiagram_map_isOpenImmersion
    {s t : (NonemptyChartSet ι)ᵒᵖ} (f : s ⟶ t) :
    IsOpenImmersion ((finiteIntersectionSchemeDiagram U).map f) := by
  change IsOpenImmersion (X.homOfLE (finiteIntersectionOpen_antitone U (leOfHom f.unop)))
  infer_instance

/-- Nonempty finite intersections of affine charts remain affine on a separated scheme. -/
theorem finiteIntersectionSchemeDiagram_isAffine [X.IsSeparated]
    (hU : ∀ i, IsAffineOpen (U i)) (s : (NonemptyChartSet ι)ᵒᵖ) :
    IsAffine ((finiteIntersectionSchemeDiagram U).obj s) :=
  IsAffineOpen.biInf (s.unop.val : Set ι) s.unop.val.finite_toSet s.unop.property
    (fun i _ ↦ hU i)

/-- The intersection objects cover whenever the original charts cover. -/
theorem finiteIntersectionOpen_cover (hU : iSup U = ⊤) :
    (⨆ s, finiteIntersectionOpen U s) = ⊤ := by
  apply top_unique
  rw [← hU]
  apply iSup_le
  intro i
  exact le_iSup_of_le (singletonChartSet i) (by simp)

/-- Unions give the actual pullback intersections over every common chart intersection. -/
theorem finiteIntersectionOpen_isPullback (r s t : NonemptyChartSet ι)
    (hrs : r ≤ s) (hrt : r ≤ t) :
    IsPullback
      (X.homOfLE (finiteIntersectionOpen_antitone U
        (le_unionChartSet_left s t)))
      (X.homOfLE (finiteIntersectionOpen_antitone U
        (le_unionChartSet_right s t)))
      (X.homOfLE (finiteIntersectionOpen_antitone U hrs))
      (X.homOfLE (finiteIntersectionOpen_antitone U hrt)) := by
  classical
  apply (isPullback_opens_inf_le (finiteIntersectionOpen_antitone U hrs)
    (finiteIntersectionOpen_antitone U hrt)).of_iso
    (X.isoOfEq (finiteIntersectionOpen_union U s t).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [← cancel_mono (finiteIntersectionOpen U s).ι]
  · simp [← cancel_mono (finiteIntersectionOpen U t).ι]
  · simp
  · simp

end FLT.Mazur.Approximation

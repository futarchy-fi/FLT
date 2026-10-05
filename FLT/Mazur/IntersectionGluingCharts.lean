/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionDiagramGluing

/-!
# Actual overlaps of the glued intersection charts

In a locally directed intersection diagram, the union of chart labels
represents the intersection of the two chart images in the colimit.
This identifies the model coordinate rings on actual overlaps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {ι : Type v} [Finite ι]
  (F : (NonemptyChartSet ι)ᵒᵖ ⥤ Scheme.{u})
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
  [(F ⋙ Scheme.forget).IsLocallyDirected]

/-- The inverse image of a glued chart is the image of the union-label chart. -/
theorem intersection_colimit_preimage (s t : NonemptyChartSet ι) :
    colimit.ι F (.op s) ⁻¹' Set.range (colimit.ι F (.op t)) =
      Set.range (F.map (homOfLE (le_unionChartSet_left s t)).op) := by
  classical
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, ft, fs, z, _, hx⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hy
    have hu : unionChartSet s t ≤ k.unop :=
      Finset.union_subset (leOfHom fs.unop) (leOfHom ft.unop)
    refine ⟨F.map (homOfLE hu).op z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← F.map_comp]
    have h : (homOfLE hu).op ≫ (homOfLE (le_unionChartSet_left s t)).op = fs :=
      Subsingleton.elim _ _
    rw [h, hx]
  · rintro ⟨y, rfl⟩
    refine ⟨F.map (homOfLE (le_unionChartSet_right s t)).op y, ?_⟩
    simp only [← Scheme.Hom.comp_apply, colimit.w]

/-- Union-label charts are the actual pullbacks of chart inclusions into the colimit. -/
theorem intersection_colimit_isPullback (s t : NonemptyChartSet ι) :
    IsPullback
      (F.map (homOfLE (le_unionChartSet_left s t)).op)
      (F.map (homOfLE (le_unionChartSet_right s t)).op)
      (colimit.ι F (.op s)) (colimit.ι F (.op t)) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    apply IsOpenImmersion.lift (F.map (homOfLE (le_unionChartSet_left s t)).op) c.fst
    rw [← intersection_colimit_preimage F]
    rintro x ⟨y, rfl⟩
    use c.snd y
    simp only [← Scheme.Hom.comp_apply, c.condition]
  · simp
  · intro c
    rw [← cancel_mono (colimit.ι F (.op t)), Category.assoc, colimit.w,
      ← colimit.w F (homOfLE (le_unionChartSet_left s t)).op,
      IsOpenImmersion.lift_fac_assoc, c.condition]
  · intro c m h₁ h₂
    simpa [← cancel_mono (F.map (homOfLE (le_unionChartSet_left s t)).op)]

/-- The union chart image is the intersection of the two chart images. -/
theorem intersection_colimit_range (s t : NonemptyChartSet ι) :
    Set.range (colimit.ι F (.op (unionChartSet s t))) =
      Set.range (colimit.ι F (.op s)) ∩ Set.range (colimit.ι F (.op t)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · refine ⟨F.map (homOfLE (le_unionChartSet_left s t)).op y, ?_⟩
      simp only [← Scheme.Hom.comp_apply, colimit.w]
    · refine ⟨F.map (homOfLE (le_unionChartSet_right s t)).op y, ?_⟩
      simp only [← Scheme.Hom.comp_apply, colimit.w]
  · rintro ⟨⟨y, rfl⟩, ht⟩
    have hy : y ∈ Set.range (F.map (homOfLE (le_unionChartSet_left s t)).op) := by
      rw [← intersection_colimit_preimage F s t]
      exact ht
    obtain ⟨z, rfl⟩ := hy
    refine ⟨z, ?_⟩
    simp only [← Scheme.Hom.comp_apply, colimit.w]

end FLT.Mazur.Approximation

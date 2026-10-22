/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothBaseChangeDimensionOpen

/-!
# Relative dimension on neighborhoods of a recovered marking

Relative-dimension opens can be joined without losing their dimension.
A marking recovered in the dimension-d smooth part therefore has a single
such neighborhood in the fixed model, before enlarging its coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeDimensionNeighborhood
set_option backward.isDefEq.respectTransparency false

/-- The union of relative-dimension-d opens still has relative dimension d. -/
theorem iSup_relativeDimension {X S : Scheme} (p : X ⟶ S) (d : ℕ)
    {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, SmoothOfRelativeDimension d ((V i).ι ≫ p)) :
    SmoothOfRelativeDimension d ((⨆ i, V i).ι ≫ p) := by
  let U := ⨆ i, V i
  have hc : (⨆ i, U.ι ⁻¹ᵁ V i) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d)
    (fun i ↦ U.ι ⁻¹ᵁ V i) hc
  intro i
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension d) (hV i) _

/-- Smooth recovered dimension gives a model neighborhood of the entire recovered marking. -/
theorem exists_marking_open {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    {X Y : Scheme} (p : Y ⟶ Spec (.of R)) (r : X ⟶ Spec (.of A)) (a : X ⟶ Y)
    (h : IsPullback a r p (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    [LocallyOfFinitePresentation p] (d : ℕ)
    [SmoothOfRelativeDimension d ((a ⁻¹ᵁ p.smoothLocus).ι ≫ r)]
    (s : Spec (.of A) ⟶ X) (hs : (s ≫ a) ⁻¹ᵁ p.smoothLocus = ⊤) :
    ∃ V : Y.Opens, (s ≫ a) ⁻¹ᵁ V = ⊤ ∧ SmoothOfRelativeDimension d (V.ι ≫ p) := by
  have hx (x : Spec (.of A)) : a (s x) ∈ p.smoothLocus :=
    hs.ge (Set.mem_univ x)
  choose V hV hd using fun x ↦
    SmoothBaseChangeDimensionOpen.exists_open_at_smoothPoint p r a h d (s x) (hx x)
  refine ⟨⨆ x, V x, ?_, iSup_relativeDimension p d V hd⟩
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hV x⟩

end FLT.Mazur.RelativeDimensionNeighborhood

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeSmoothLocus
public import FLT.Mazur.PolygonCoconeComparison

/-!
# The Laurent opens of the polygon atlas

The specified normalization restricts to pairwise disjoint open Laurent
components. Their union is exactly the smooth locus, also for the one-gon.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur
variable (K : Type u) [Field K]

namespace PolygonPinching
/-- The full Laurent chart in the specified projective-line component. -/
def torusToComponent : MultiplicativeGroupScheme.gm K ⟶ component K :=
  Over.homMk (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) (by
    change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
      ProjectiveLine.toBase K = OneGonGluing.torusToBase K
    rw [Category.assoc, ProjectiveLine.left_toBase, OneGonNormalization.overlapLeft_toBase])
end PolygonPinching

namespace PolygonAtlas
/-- The specified Laurent component map into the actual atlas. -/
def torus (n : ℕ) [NeZero n] (i : Fin n) :
    MultiplicativeGroupScheme.gm K ⟶ polygon K n :=
  PolygonPinching.torusToComponent K ≫ PolygonPinching.componentι K n i ≫ normalization K n

@[reassoc]
theorem torus_one (i : Fin 1) : (torus K 1 i).left = OneGonGluing.torus K := by
  change (PolygonPinching.torusToComponent K ≫
    PolygonPinching.componentι K 1 i ≫ OneGonNormalization.normalizationOver K).left = _
  rw [OneGonNormalization.componentι_normalizationOver]
  exact OneGonNormalization.torus_normalization K

@[reassoc]
theorem torus_cyclic (n : ℕ) [NeZero n] (h : 2 ≤ n) (i : Fin n) :
    (torus K n i ≫ (cyclicIso K n h).hom).left =
      PolygonNodeBranches.left K ≫ PolygonCyclicAtlas.chart K n h i := by
  change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
    (PolygonPinching.componentι K n i ≫ normalization K n ≫ (cyclicIso K n h).hom).left = _
  rw [Category.assoc, left_component, PolygonCyclicAtlas.overlap_firstBranch_assoc]

instance torus_isOpenImmersion (n : ℕ) [NeZero n] (i : Fin n) :
    IsOpenImmersion (torus K n i).left := by
  rcases n with _ | (_ | n)
  · exact False.elim (NeZero.ne 0 rfl)
  · rw [torus_one]; infer_instance
  · have he := torus_cyclic K (n + 2) (by omega) i
    change (torus K (n + 2) i).left ≫ 𝟙 _ = _ at he
    rw [Category.comp_id] at he
    rw [he]; infer_instance

/-- Naturality of the smooth locus at a point of an open chart. -/
theorem mem_smooth_iff {U X S : Scheme.{u}} (f : U ⟶ X) (g : X ⟶ S)
    [IsOpenImmersion f] [LocallyOfFinitePresentation g] (x : U) :
    f x ∈ g.smoothLocus ↔ x ∈ (f ≫ g).smoothLocus := by
  change x ∈ f ⁻¹ᵁ g.smoothLocus ↔ _
  rw [Scheme.Hom.preimage_smoothLocus_eq]

/-- Each full Laurent component is contained in the smooth locus. -/
theorem range_torus_subset (n : ℕ) [NeZero n] (i : Fin n) :
    Set.range (torus K n i).left ⊆ (polygon K n).hom.smoothLocus := by
  rintro _ ⟨x, rfl⟩
  apply (mem_smooth_iff (torus K n i).left (polygon K n).hom x).mpr
  simp only [Over.w, Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- Distinct Laurent edges remain disjoint after cyclic gluing, including n=2. -/
theorem cyclic_disjoint (n : ℕ) (h : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Set.range (PolygonNodeBranches.left K ≫ PolygonCyclicAtlas.chart K n h i))
      (Set.range (PolygonNodeBranches.left K ≫ PolygonCyclicAtlas.chart K n h j)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, he⟩
  have he' : PolygonCyclicAtlas.chart K n h i (PolygonNodeBranches.left K x) =
      PolygonCyclicAtlas.chart K n h j (PolygonNodeBranches.left K y) := he.symm
  rcases (PolygonCyclicAtlas.charts_eq_iff K n h hij _ _).mp he' with
    ⟨z, _, _, hz⟩ | ⟨z, _, hz, _⟩
  · exact Set.disjoint_left.mp (PolygonNodeBranches.disjoint_ranges K)
      ⟨y, rfl⟩ ⟨(ProjectiveLine.inversion K).hom z, hz⟩
  · exact Set.disjoint_left.mp (PolygonNodeBranches.disjoint_ranges K)
      ⟨x, rfl⟩ ⟨(ProjectiveLine.inversion K).hom z, hz⟩

/-- The prescribed full Laurent components have disjoint ranges. -/
theorem disjoint_torus (n : ℕ) [NeZero n] {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Set.range (torus K n i).left) (Set.range (torus K n j).left) := by
  rcases n with _ | (_ | n)
  · exact False.elim (NeZero.ne 0 rfl)
  · exact (hij (Fin.ext (by omega))).elim
  · have hi := torus_cyclic K (n + 2) (by omega) i
    have hj := torus_cyclic K (n + 2) (by omega) j
    change (torus K (n + 2) i).left ≫ 𝟙 _ = _ at hi
    change (torus K (n + 2) j).left ≫ 𝟙 _ = _ at hj
    rw [Category.comp_id] at hi hj
    rw [hi, hj]
    exact cyclic_disjoint K (n + 2) (by omega) hij

/-- Smooth points of the cyclic atlas lie on one of its full Laurent edges. -/
theorem cyclic_smooth_cover (n : ℕ) (h : 2 ≤ n)
    (x : PolygonCyclicAtlas.scheme K n h)
    (hx : letI := PolygonPinching.cyclic_lfp K n h
      x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus) :
    ∃ i y, (PolygonNodeBranches.left K ≫ PolygonCyclicAtlas.chart K n h i) y = x := by
  let := PolygonPinching.cyclic_lfp K n h
  obtain ⟨i, z, rfl⟩ := PolygonCyclicAtlas.charts_cover K n h x
  rw [mem_smooth_iff] at hx
  simp only [PolygonCyclicAtlas.chart_toBase] at hx
  change z ∈ ((PolygonNodePresentation.aToBase K).smoothLocus : Set _) at hx
  rw [PolygonNodePresentation.a_smooth_complement,
    ← PolygonNodePresentation.a_zeroLocus_origin,
    ← PolygonNodeBranches.branches_cover_complement] at hx
  rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨i, y, rfl⟩
  · refine ⟨finRotate n i, (ProjectiveLine.inversion K).inv y, ?_⟩
    rw [PolygonCyclicAtlas.overlap, Equiv.symm_apply_apply]
    simp only [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]

/-- The one-gon smooth locus is its entire Laurent chart, including coordinate one. -/
theorem one_smooth_range :
    let := PolygonPinching.oneGon_lfp K
    ((OneGonGluing.toBase K).smoothLocus : Set (OneGonGluing.scheme K)) =
      Set.range (OneGonGluing.torus K) := by
  let := PolygonPinching.oneGon_lfp K
  apply Set.Subset.antisymm
  · intro x hx
    rcases OneGonGluing.charts_cover K x with ⟨z, rfl⟩ | hz
    · have hx := (mem_smooth_iff (OneGonGluing.node K) (OneGonGluing.toBase K) z).mp hx
      simp only [OneGonGluing.node_toBase] at hx
      change z ∈ ((PolygonNodePresentation.bToBase K).smoothLocus : Set _) at hx
      rw [PolygonNodePresentation.b_smooth_complement,
        ← PolygonNodePresentation.b_zeroLocus_origin,
        ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
        ← PolygonNodePresentation.range_bPuncture] at hx
      obtain ⟨y, rfl⟩ := hx
      refine ⟨OneGonTransition.toTorus K y, ?_⟩
      exact congrArg (fun f ↦ f y) (OneGonGluing.overlap_condition K).symm
    · exact hz
  · have ht := range_torus_subset K 1 0
    rw [torus_one] at ht
    exact ht

/-- Exactly the disjoint full Laurent components form the smooth locus. -/
theorem smooth_range (n : ℕ) [NeZero n] :
    ((polygon K n).hom.smoothLocus : Set (polygon K n).left) =
      ⋃ i : Fin n, Set.range (torus K n i).left := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases n with _ | (_ | n)
    · exact False.elim (NeZero.ne 0 rfl)
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      rw [torus_one]
      exact (Set.ext_iff.mp (one_smooth_range K) x).mp hx
    · obtain ⟨i, y, hy⟩ := cyclic_smooth_cover K (n + 2) (by omega) x hx
      refine Set.mem_iUnion.mpr ⟨i, y, ?_⟩
      have he := torus_cyclic K (n + 2) (by omega) i
      change (torus K (n + 2) i).left ≫ 𝟙 _ = _ at he
      rw [Category.comp_id] at he
      rw [he]
      exact hy
  · exact Set.iUnion_subset fun i ↦ range_torus_subset K n i

end PolygonAtlas
end FLT.Mazur

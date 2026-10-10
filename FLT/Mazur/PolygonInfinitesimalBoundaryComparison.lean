/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryDivisor
public import FLT.Mazur.PolygonCyclicPushout
public import FLT.Mazur.PolygonInfinitesimalDivisor
public import FLT.Mazur.PolygonInfinitesimalSpecialFiber

/-!
# The marking divisor on the original closed polygon

The zero-fiber comparison carries the original normalization unit sections to
the actual smoothing markings. Pulling back the whole infinitesimal divisor
therefore recovers the previously constructed polygon boundary divisor exactly.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing FCurve

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- Each original normalization unit section is the corresponding zero-stage marking. -/
@[reassoc] theorem boundarySection_zeroFiberIso (i : Fin n) (a : Kˣ) :
    PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h) a i ≫
      (zeroFiberIso K n h).hom = marking K 0 n h i a := by
  unfold PolygonMarkedSections.sectionMap
  rw [PolygonCyclicAtlas.componentι_normalization]
  change (ProjectiveLineActionSpecialization.unitPoint K a ≫
    ((ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
      PolygonCyclicAtlas.componentMap K n h i)) ≫ _ = _
  simp only [Category.assoc, PolygonCyclicAtlas.left_componentMap_assoc,
    PolygonCyclicAtlas.overlap_firstBranch_assoc, chart_zeroFiberIso]
  rw [← Category.assoc (PolygonNodeBranches.left K), specialFiberIso_left]
  change markedTorusSection a ≫ leftBranchOpen K 0 ≫ chart K 0 n h i = _
  rw [← Category.assoc, markedTorusSection_left, marking]

/-- The original boundary ideal is exactly the zero-stage marking divisor pullback. -/
theorem markingDivisor_zeroFiberIso (a : Fin n → Kˣ) :
    (markingDivisor K 0 n h a).comap (zeroFiberIso K n h).hom =
      PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h) a := by
  let _ := PolygonInfinitesimalSeparated.separated K 0 n h
  have H : IsPullback (zeroFiberIso K n h).hom (PolygonCyclicAtlas.toBase K n h)
      (toBase K 0 n h) (𝟙 _) := IsPullback.of_horiz_isIso
        ⟨by rw [zeroFiberIso_base, Category.comp_id]⟩
  exact section_prod_comap_of_cartesian H Finset.univ _ _
    (fun i ↦ PolygonMarkedSections.section_base K n _ (a i) i)
    (fun i ↦ marking_base K 0 n h i (a i))
    (fun i ↦ by rw [Category.id_comp]; exact boundarySection_zeroFiberIso K n h i (a i))

end FLT.Mazur.PolygonInfinitesimal

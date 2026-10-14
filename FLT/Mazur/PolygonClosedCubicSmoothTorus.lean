/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicTorus
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# The smooth locus of the original closed cubic is its full retained torus

The global cubic comparison preserves the original residue-field structure
map. Smoothness therefore transports to the one-gon's actual Laurent open.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "E" => closedPointContractionCubicIso K n h i
local notation "c" => Over.hom (closedPointCubicOver K n h i)

instance closedPointCubicOver_lfp : LocallyOfFinitePresentation (c) := by
  change LocallyOfFinitePresentation (pullback.snd
    (WeierstrassIntegralChart.integralCurveStructure (completePointWeierstrassCurve K n h i)) _)
  infer_instance

/-- The full smooth open is exactly the actual transported Laurent torus. -/
theorem closedPointCubic_smoothLocus_eq_torus :
    (c).smoothLocus = (closedPointCubicTorus K n h i).opensRange := by
  ext y
  obtain ⟨z, rfl⟩ := (E).hom.surjective y
  have he := PolygonAtlas.mem_smooth_iff (E).hom (c) z
  simp only [closedPointContractionCubicIso_over] at he
  change (E).hom z ∈ (c).smoothLocus ↔ _
  rw [he]
  change z ∈ ((PolygonAtlas.polygon K 1).hom.smoothLocus : Set _) ↔ _
  rw [PolygonAtlas.smooth_range]
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨j, t, ht⟩
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    refine ⟨t, ?_⟩
    change (E).hom ((PolygonAtlas.torus K 1 0).left t) = (E).hom z
    exact congrArg (E).hom ht
  · rintro ⟨t, ht⟩
    refine ⟨0, t, (E).hom.isOpenEmbedding.injective ?_⟩
    exact ht

/-- The original closed contraction is unchanged on the entire actual smooth cubic. -/
theorem closedPointToCubic_smooth_isIso :
    IsIso ((closedPointToCubic K n h i) ∣_ (c).smoothLocus) := by
  rw [closedPointCubic_smoothLocus_eq_torus]
  exact closedPointCubicTorus_isIso K n h i

end FLT.Mazur.PolygonInfinitesimalStages

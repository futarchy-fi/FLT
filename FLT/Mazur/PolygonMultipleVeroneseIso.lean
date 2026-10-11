/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseMultipleCharts
public import FLT.Mazur.GradedDegreeProjIso

/-!
# Global comparison of complete compatible Veronese models

The original common-degree inclusion gives a global isomorphism. Its two
maps are glued from the actual chart isomorphisms, using whole-Proj coverage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q r : ℕ) [NeZero q] (hr : 0 < r)

/-- The complete models are globally isomorphic through their actual common-degree inclusion. -/
def multipleVeroneseProjIso :
    Proj (compatibleVeroneseGrade R n h q) ≅ Proj (compatibleVeroneseGrade R n h (q * r)) :=
  GradedDegreeProjIso.iso _ _ (multipleVeroneseInclusion R n h q r) r
    (multipleVeroneseInclusion_mem R n h q r) hr
    (multipleVeronese_common_charts_cover R n h q r hr)
    (fun d s hs _ ↦ ⟨multipleVeroneseChartMap_injective R n h q r hr s,
      multipleVeroneseChartMap_surjective R n h q r d s hs⟩)

/-- The forward global comparison retains the original common-degree fraction map. -/
@[reassoc]
theorem multipleVeroneseProjIso_hom_chart {d : ℕ}
    (s : CompatibleVeroneseSections R n h (q * r))
    (hs : s ∈ compatibleVeroneseGrade R n h (q * r) d) (hd : 0 < d) :
    Proj.awayι (compatibleVeroneseGrade R n h q) (multipleVeroneseInclusion R n h q r s)
        (multipleVeroneseInclusion_mem R n h q r d s hs) (Nat.mul_pos hr hd) ≫
      (multipleVeroneseProjIso R n h q r hr).hom =
        Spec.map (CommRingCat.ofHom (multipleVeroneseChartMap R n h q r s)) ≫
          Proj.awayι (compatibleVeroneseGrade R n h (q * r)) s hs hd :=
  GradedDegreeProjMap.awayι_map _ _ _ _ _ _ _ s hs hd

/-- The inverse global comparison retains the inverse original chart isomorphism. -/
@[reassoc]
theorem multipleVeroneseProjIso_inv_chart {d : ℕ}
    (s : CompatibleVeroneseSections R n h (q * r))
    (hs : s ∈ compatibleVeroneseGrade R n h (q * r) d) (hd : 0 < d) :
    Proj.awayι (compatibleVeroneseGrade R n h (q * r)) s hs hd ≫
        (multipleVeroneseProjIso R n h q r hr).inv =
      Spec.map (CommRingCat.ofHom
        (multipleVeroneseChartIso R n h q r hr d s hs).symm.toRingHom) ≫
          Proj.awayι (compatibleVeroneseGrade R n h q)
            (multipleVeroneseInclusion R n h q r s)
            (multipleVeroneseInclusion_mem R n h q r d s hs) (Nat.mul_pos hr hd) := by
  rw [multipleVeroneseProjIso, GradedDegreeProjIso.iso,
    GradedDegreeProjIso.awayι_inverse]
  unfold GradedDegreeProjInverseCharts.inverseChart
  congr 1
  let _ : IsIso (CommRingCat.ofHom (multipleVeroneseChartMap R n h q r s)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (multipleVeroneseChartIso R n h q r hr d s hs).bijective
  apply (cancel_epi (Spec.map
    (CommRingCat.ofHom (multipleVeroneseChartMap R n h q r s)))).mp
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom (multipleVeroneseChartMap R n h q r s)) ≫
    inv (Spec.map (CommRingCat.ofHom (multipleVeroneseChartMap R n h q r s))) = _
  rw [IsIso.hom_inv_id]
  change _ = Spec.map (CommRingCat.ofHom
    ((multipleVeroneseChartIso R n h q r hr d s hs).toRingHom.comp
      (multipleVeroneseChartIso R n h q r hr d s hs).symm.toRingHom))
  simp only [RingEquiv.toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id]

end FLT.Mazur.PolygonInfinitesimalStages

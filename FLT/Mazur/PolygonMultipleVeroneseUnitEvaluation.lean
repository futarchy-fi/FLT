/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleVeroneseIso
public import FLT.Mazur.GradedDegreeProjUnitNaturality

/-!
# Common-step comparison retains actual stage coordinate evaluations

Every original finite-stage ring evaluation commutes with the global complete
model comparison on each invertible common homogeneous coordinate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleEval
variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q r : ℕ) [NeZero q]

/-- Inclusion keeps the entire original stage evaluation as a ring homomorphism. -/
theorem multipleVeroneseInclusion_eval_comp (m : ℕ) :
    (compatibleVeroneseEval R n h q m).comp (multipleVeroneseInclusion R n h q r) =
      compatibleVeroneseEval R n h (q * r) m := by
  apply RingHom.ext
  intro s
  exact multipleVeroneseInclusion_eval R n h q r m s

/-- The global isomorphism retains any actual unit-coordinate map through a finite stage. -/
@[reassoc]
theorem multipleVeroneseProjIso_stageUnit (hr : 0 < r) (m : ℕ)
    {X : Scheme} (φ : boundaryGradedSections R n h m →+* Γ(X, ⊤)) {d : ℕ}
    (s : CompatibleVeroneseSections R n h (q * r))
    (hs : s ∈ compatibleVeroneseGrade R n h (q * r) d) (hd : 0 < d)
    (hu : IsUnit (φ (compatibleVeroneseEval R n h (q * r) m s))) :
    GradedProjUnitChart.toProj (compatibleVeroneseGrade R n h q)
        (φ.comp (compatibleVeroneseEval R n h q m)) (multipleVeroneseInclusion R n h q r s)
        (by simpa only [RingHom.comp_apply, multipleVeroneseInclusion_eval] using hu)
        (multipleVeroneseInclusion_mem R n h q r d s hs) (Nat.mul_pos hr hd) ≫
      (multipleVeroneseProjIso R n h q r hr).hom =
        GradedProjUnitChart.toProj (compatibleVeroneseGrade R n h (q * r))
          (φ.comp (compatibleVeroneseEval R n h (q * r) m)) s hu hs hd := by
  change _ ≫ GradedDegreeProjMap.map _ _ _ _ _ _ _ = _
  rw [GradedDegreeProjUnitNaturality.toProj_map _ _ _ r
    (multipleVeroneseInclusion_mem R n h q r) hr
    (multipleVeronese_common_charts_cover R n h q r hr)
    (φ.comp (compatibleVeroneseEval R n h q m)) s hs hd]
  simp only [RingHom.comp_assoc, multipleVeroneseInclusion_eval_comp]

end FLT.Mazur.PolygonInfinitesimalStages

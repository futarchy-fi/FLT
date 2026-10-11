/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleCoefficientStageOpens
public import FLT.Mazur.PolygonMultipleStageOpenDetection
public import FLT.Mazur.GradedDegreeProjMap

/-!
# Global coefficient morphism at a common exact step

The original coefficient-image charts cover the entire complete model: they
cover its original zeroth stage, and proper specialization detects open covers.
Their actual fraction maps therefore glue to a global coefficient morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n)
  [NeZero n] (q : ℕ) [NeZero q]
  (hK : exactVeroneseStep K n h ∣ q) (hL : exactVeroneseStep L n h ∣ q)

include hK hL

/-- The actual coefficient image covers the whole complete model at a shared exact step. -/
theorem coefficientImage_complete_cover :
    (⨆ i : Σ d : PNat, compatibleVeroneseGrade K n h q d,
      Proj.basicOpen (compatibleVeroneseGrade L n h q)
        (compatibleVeroneseCoefficientMap f n h q i.2)) = ⊤ := by
  apply multipleStage_open_eq_top L n h q hL
  rw [Scheme.Hom.preimage_iSup]
  exact coefficientImage_stage_cover f n h q hK hL 0

omit hK hL [NeZero n] [NeZero q] in
/-- Coefficient change is a degree-changing ring map with scale one. -/
theorem compatibleVeroneseCoefficientMap_mem_scaled (d : ℕ)
    (s : CompatibleVeroneseSections K n h q) (hs : s ∈ compatibleVeroneseGrade K n h q d) :
    compatibleVeroneseCoefficientMap f n h q s ∈ compatibleVeroneseGrade L n h q (1 * d) := by
  rw [Nat.one_mul]
  exact (compatibleVeroneseCoefficientGradedMap f n h q).map_mem hs

/-- The global complete coefficient morphism, built from the original coefficient fraction maps. -/
def multipleCoefficientProjMap :
    Proj (compatibleVeroneseGrade L n h q) ⟶ Proj (compatibleVeroneseGrade K n h q) :=
  GradedDegreeProjMap.map _ _ (compatibleVeroneseCoefficientMap f n h q) 1
    (compatibleVeroneseCoefficientMap_mem_scaled f n h q) Nat.zero_lt_one
    (coefficientImage_complete_cover f n h q hK hL)

/-- The constructed global map retains the actual coefficient fraction map on every image chart. -/
@[reassoc]
theorem multipleCoefficientProjMap_chart {d : ℕ}
    (s : CompatibleVeroneseSections K n h q) (hs : s ∈ compatibleVeroneseGrade K n h q d)
    (hd : 0 < d) :
    Proj.awayι (compatibleVeroneseGrade L n h q) (compatibleVeroneseCoefficientMap f n h q s)
        ((compatibleVeroneseCoefficientGradedMap f n h q).map_mem hs) hd ≫
      multipleCoefficientProjMap f n h q hK hL =
        GradedDegreeProjOverlap.chartMap _ _ (compatibleVeroneseCoefficientMap f n h q) 1
          (compatibleVeroneseCoefficientMap_mem_scaled f n h q) s hs hd := by
  simpa only [Nat.one_mul, multipleCoefficientProjMap] using
    GradedDegreeProjMap.awayι_map _ _ _ 1
    (compatibleVeroneseCoefficientMap_mem_scaled f n h q) Nat.zero_lt_one
    (coefficientImage_complete_cover f n h q hK hL) s hs hd

end FLT.Mazur.PolygonInfinitesimalStages

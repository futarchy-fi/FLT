/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthOriginalOpen
public import FLT.Mazur.WeierstrassSuccessiveCenterScaling

/-!
# Normalizing the actual successive center and original contraction

The preceding chart comparison retains the full three-generator center and
the original cubic morphism. Thus local action lifts can be transported to
finite-depth charts without changing their center or their contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ k)
  (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)
local notation "v" => WeierstrassSuccessiveX.previousDepthEquiv π k hπ W
  d.b3 d.b4 d.b6 e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6
  e.factor3 e.factor4 e.factor6

/-- The successive center expressed directly on the actual preceding depth chart. -/
def depthCenter : Ideal A := Ideal.span {algebraMap R A π,
  WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6,
  WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6}

/-- Normalization retains the complete ideal, including its scheme structure. -/
theorem depthCenter_map_previous :
    (depthCenter d).map (v).toRingHom =
      WeierstrassSuccessiveX.modificationCenter W (π ^ k) π e.b3 e.b4 e.b6 := by
  simp [depthCenter, Ideal.map_span, WeierstrassSuccessiveX.previousDepthEquiv,
    WeierstrassSuccessiveX.modificationCenter]

/-- The normalized coefficient factors give the preceding chart's original map. -/
theorem previousFromOriginal :
    (v).toAlgHom.comp
        (WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
          d.factor3 d.factor4 d.factor6) =
      WeierstrassDilatation.fromOriginal W (π ^ k) (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)
        (by rw [← factor3_step hπ d e]; exact d.factor3)
        (by rw [← factor4_step hπ d e]; exact d.factor4)
        (by rw [← factor6_step hπ d e]; exact d.factor6) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · simp [WeierstrassSuccessiveX.previousDepthEquiv]
  · simp [WeierstrassSuccessiveX.previousDepthEquiv]
  · simp [WeierstrassDilatation.fromOriginal]

/-- The chart isomorphism is compatible with the actual original cubic contraction. -/
@[reassoc] theorem previousChartIso_toCurve :
    (previousChartIso hπ d e).hom ≫ toCurve d =
      WeierstrassDilatation.toCurve W (π ^ k) (π * e.b3) (π * e.b4) (π ^ 2 * e.b6)
        (by rw [← factor3_step hπ d e]; exact d.factor3)
        (by rw [← factor4_step hπ d e]; exact d.factor4)
        (by rw [← factor6_step hπ d e]; exact d.factor6) := by
  change Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (previousFromOriginal hπ d e)

end FLT.Mazur.WeierstrassDividedDepth

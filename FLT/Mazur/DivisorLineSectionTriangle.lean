/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Commuting triangles of canonical line comparisons

Section-preserving comparisons commute with a specified equality of composite
scheme morphisms. Their actual tensor-power comparisons retain this equality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y Z : Scheme}

/-- The exact compositor and transport equation for a triangle of actual line comparisons. -/
def LinePullbackTriangle (f : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ Z) (w : f ≫ g = r)
    {A : Z.Modules} {B : Y.Modules} {C : X.Modules}
    (e : (pullback g).obj A ≅ B) (v : (pullback f).obj B ≅ C)
    (k : (pullback r).obj A ≅ C) : Prop :=
  (pullbackComp f g).symm.app A ≪≫ (pullback f).mapIso e ≪≫ v =
    (pullbackCongr w).app A ≪≫ k

/-- Section-preserving Cartier-line comparisons satisfy the triangle equation. -/
theorem divisorLineSectionCompatible_triangle
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ Z) (w : f ≫ g = r)
    {I : Z.IdealSheafData} {J : Y.IdealSheafData} {K : X.IdealSheafData}
    {hI : EffectiveCartier I} {hJ : EffectiveCartier J} {hK : EffectiveCartier K}
    {e : (pullback g).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ}
    {v : (pullback f).obj (divisorLineBundle J hJ) ≅ divisorLineBundle K hK}
    {k : (pullback r).obj (divisorLineBundle I hI) ≅ divisorLineBundle K hK}
    (he : DivisorLineSectionCompatible g hI hJ e)
    (hv : DivisorLineSectionCompatible f hJ hK v)
    (hk : DivisorLineSectionCompatible r hI hK k) :
    LinePullbackTriangle f g r w e v k :=
  (he.comp hv).ext (hk.congr w)

/-- Coherence of the original line triangle propagates to every actual tensor power. -/
theorem LinePullbackTriangle.tensorPower
    {f : X ⟶ Y} {g : Y ⟶ Z} {r : X ⟶ Z} {w : f ≫ g = r}
    {A : Z.Modules} {B : Y.Modules} {C : X.Modules}
    {e : (pullback g).obj A ≅ B} {v : (pullback f).obj B ≅ C}
    {k : (pullback r).obj A ≅ C} (he : LinePullbackTriangle f g r w e v k) (d : ℕ) :
    LinePullbackTriangle f g r w (tensorPowerPullbackComparison g e d)
      (tensorPowerPullbackComparison f v d) (tensorPowerPullbackComparison r k d) := by
  change _ = _ at he
  unfold LinePullbackTriangle
  rw [tensorPowerPullbackComparison_comp, he, tensorPowerPullbackComparison_congr]

end FLT.Mazur.FCurve

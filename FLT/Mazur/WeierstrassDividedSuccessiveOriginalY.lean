/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthAffine
public import FLT.Mazur.WeierstrassDividedDepthBoundary

/-!
# The actual original y function on a successive chart

The affine cubic y coordinate contracts to the full scaled product of the
horizontal coordinate and slope. Its principal open retains that scale,
including when the uniformizer becomes zero after coefficient extension.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
open WeierstrassSuccessiveX

/-- The full original y coordinate, including its integral scale. -/
def successiveOriginalY : Coordinate W (π ^ k) π e.b3 e.b4 e.b6 :=
  algebraMap R _ (π ^ k) *
    (coord W (π ^ k) π e.b3 e.b4 e.b6 2 * coord W (π ^ k) π e.b3 e.b4 e.b6 1)

/-- The actual affine contraction pulls back D(y) to the full scaled-product principal open. -/
theorem xContraction_originalY_preimage :
    (xContraction hπ d e ≫ toAffine d) ⁻¹'
      (PrimeSpectrum.basicOpen (WeierstrassIntegralChart.coord W 2 1) :
        Set (PrimeSpectrum (WeierstrassIntegralChart.Coordinate W 2))) =
        (PrimeSpectrum.basicOpen (successiveOriginalY e) :
          Set (PrimeSpectrum (Coordinate W (π ^ k) π e.b3 e.b4 e.b6))) := by
  ext z
  change (fromDivided W (π ^ k) π e.b3 e.b4 e.b6)
    ((WeierstrassDilatation.parameterEquiv W (π ^ k) (π ^ k)
      d.b3 d.b4 d.b6 (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
      (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e))
        ((WeierstrassDilatation.fromOriginal W (π ^ k) d.b3 d.b4 d.b6
          d.factor3 d.factor4 d.factor6) (WeierstrassIntegralChart.coord W 2 1))) ∉
            z.asIdeal ↔ successiveOriginalY e ∉ z.asIdeal
  rw [WeierstrassDilatation.fromOriginal_y, map_mul, AlgEquiv.commutes,
    WeierstrassDilatation.parameterEquiv_y, map_mul, AlgHom.commutes, fromDivided_y]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothDividedSecantResidue
public import FLT.Mazur.WeierstrassSmoothHorizontalResiduePoint

/-!
# The terminal secant specialization retains the original smooth point

The concrete residue factor preserves the entire smooth Y presentation.
Its scheme point is the independent smooth residue parameter with the original
coefficient projection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k ≤ depth)
  (hp : 2 * k = depth)
local notation "K" => ResidueField R
local notation "S" => SmoothDividedProductRing W (π ^ k) d.b3 d.b4 d.b6
local notation "T" => SmoothDividedSecantRing d
local notation "p" => smoothDividedPoint W (π ^ k) d.b3 d.b4 d.b6
local notation "e" => smoothDividedProductResidue D d hk0 hk hp

/-- The product specialization preserves the complete original smooth point. -/
theorem smoothDividedProductResidue_point :
    Spec.map (CommRingCat.ofHom (e).toRingHom) ≫ p =
      smoothHorizontalResiduePoint D (by omega) ≫ originalSmoothCoefficientMap K W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have hpoint : p ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom
        (smoothDividedY W (π ^ k) d.b3 d.b4 d.b6).toRingHom) ≫
          integralCurveChart W 1 :=
    (smoothDividedLeft_inclusion W (π ^ k) d.b3 d.b4 d.b6).symm.trans
      (smoothDivided_common W (π ^ k) d.b3 d.b4 d.b6)
  simp only [Category.assoc, hpoint, smoothHorizontalResiduePoint,
    originalSmoothCoefficientMap_inclusion, infinityResidueSmoothIso_contraction,
    infinityResidueContraction]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  exact RingHom.ext (smoothDividedProductResidue_Y D d hk0 hk hp)

/-- The actual secant residue factor gives the same independent smooth residue point. -/
theorem smoothDividedSecantResidue_point :
    Spec.map (CommRingCat.ofHom (smoothDividedSecantResidue D d hk0 hk hp).toRingHom) ≫
      smoothDividedSecantPoint d =
        smoothHorizontalResiduePoint D (by omega) ≫ originalSmoothCoefficientMap K W := by
  have he : Spec.map (CommRingCat.ofHom
        (smoothDividedSecantResidue D d hk0 hk hp).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) =
        Spec.map (CommRingCat.ofHom (e).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext (smoothDividedSecantResidue_base D d hk0 hk hp)
  simpa only [smoothDividedSecantPoint, ← Category.assoc, he] using
    smoothDividedProductResidue_point D d hk0 hk hp

end FLT.Mazur.WeierstrassIntegralChart

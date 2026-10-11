/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveIntegralCubicMaps
public import FLT.Mazur.WeierstrassSmoothHorizontalResiduePoint

/-!
# The common integral refinement retains the original smooth residue point

Both original residue factorizations carry the retained smooth parameter
to the same independent residue smooth point with its original orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hπ : π ≠ 0)
  (D : SplitNodeDepth W π depth) (hk : 2 * (k + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "S" => SmoothHorizontalProductRing W (π ^ (k + 1))
local notation "O" => SmoothHorizontalActionRing d
local notation "L" => SmoothSuccessiveActionOpen d hπ

/-- The first original factorization preserves every integral product function. -/
theorem smoothSuccessiveFirstIntegralResidue_product (q : S) :
    smoothSuccessiveFirstIntegralResidue d hπ D (Nat.zero_lt_succ k) hk
      (algebraMap O L (algebraMap S O q)) =
        smoothHorizontalFirstResidue D (k + 1) (Nat.zero_lt_succ k) hk hπ
          d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 q := by
  rw [smoothSuccessiveFirstIntegralResidue_base, smoothHorizontalIntegralFirstResidue_base]

/-- The first refinement retains the original independent smooth residue point. -/
theorem smoothSuccessiveFirstIntegralResidue_point :
    Spec.map (CommRingCat.ofHom
        (smoothSuccessiveFirstIntegralResidue d hπ D (Nat.zero_lt_succ k) hk).toRingHom) ≫
      smoothSuccessiveIntegralPoint d hπ =
        smoothHorizontalResiduePoint D (by omega) ≫ originalSmoothCoefficientMap K W := by
  have he : Spec.map (CommRingCat.ofHom
        (smoothSuccessiveFirstIntegralResidue d hπ D (Nat.zero_lt_succ k) hk).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S O)) =
        Spec.map (CommRingCat.ofHom
          (smoothHorizontalFirstResidue D (k + 1) (Nat.zero_lt_succ k) hk hπ
            d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6).toRingHom) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext (smoothSuccessiveFirstIntegralResidue_product d hπ D hk)
  simpa only [smoothSuccessiveIntegralPoint, smoothHorizontalIntegralPoint,
    ← Category.assoc, he] using
    smoothHorizontalFirstResiduePoint_original D d (Nat.zero_lt_succ k) hk hπ

/-- The second original factorization preserves every integral product function. -/
theorem smoothSuccessiveSecondIntegralResidue_product (q : S) :
    smoothSuccessiveSecondIntegralResidue d hπ D (Nat.zero_lt_succ k) hk
      (algebraMap O L (algebraMap S O q)) =
        smoothHorizontalSecondResidue D (k + 1) (Nat.zero_lt_succ k) hk hπ
          d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 q := by
  rw [smoothSuccessiveSecondIntegralResidue_base, smoothHorizontalIntegralSecondResidue_base]

/-- The second refinement retains the original independent smooth residue point. -/
theorem smoothSuccessiveSecondIntegralResidue_point :
    Spec.map (CommRingCat.ofHom
        (smoothSuccessiveSecondIntegralResidue d hπ D (Nat.zero_lt_succ k) hk).toRingHom) ≫
      smoothSuccessiveIntegralPoint d hπ =
        smoothHorizontalResiduePoint D (by omega) ≫ originalSmoothCoefficientMap K W := by
  have he : Spec.map (CommRingCat.ofHom
        (smoothSuccessiveSecondIntegralResidue d hπ D (Nat.zero_lt_succ k) hk).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S O)) =
        Spec.map (CommRingCat.ofHom
          (smoothHorizontalSecondResidue D (k + 1) (Nat.zero_lt_succ k) hk hπ
            d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6).toRingHom) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext (smoothSuccessiveSecondIntegralResidue_product d hπ D hk)
  simpa only [smoothSuccessiveIntegralPoint, smoothHorizontalIntegralPoint,
    ← Category.assoc, he] using
    smoothHorizontalSecondResiduePoint_original D d (Nat.zero_lt_succ k) hk hπ

/-- The original residue smooth point retains the integral coefficient map. -/
@[reassoc] theorem smoothSuccessiveResiduePoint_structure (hd : 0 < depth) :
    (smoothHorizontalResiduePoint D hd ≫ originalSmoothCoefficientMap K W) ≫
        integralSmoothStructure W = Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  rw [Category.assoc, originalSmoothCoefficientMap_structure,
    ← Category.assoc, smoothHorizontalResiduePoint_structure, ← Spec.map_comp]
  exact congrArg (fun f : R →+* C => Spec.map (CommRingCat.ofHom f))
    (IsScalarTower.algebraMap_eq R K C).symm

end FLT.Mazur.WeierstrassIntegralChart

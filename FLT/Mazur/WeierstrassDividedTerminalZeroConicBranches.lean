/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalZeroConicIntersection
public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicBranches
public import FLT.Mazur.WeierstrassSuccessiveXConicPunctureCompatibility

/-!
# Original initial conic parameters on the global terminal node

Both complete punctured conic parameter charts agree with the corresponding
inverted branches of the actual global terminal node chart. The first conic
parameter meets the right branch, and the second meets the left branch.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "hk'" => Nat.zero_lt_succ (start + j)

open WeierstrassSuccessiveX WeierstrassModificationX
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 d)
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "C" => zeroResidueConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "g" => globalSuccessiveTensorChart hπ data K j hj


variable (hp : 2 * (start + j + 1) < depth)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) hp (Data.b6 d) (Data.factor6 d))
local notation "ha" => D.a₁_unit.map (residue R)
local notation "f₁" => conicBoundaryFirst W₀ c ha hc
local notation "f₂" => conicBoundarySecond W₀ c ha hc
local notation "ψ" => residueNodeConicMap D (start + j) hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "G" => terminalNodeChart hπ data D (j + 1) hj hk' hk hp
local notation "ι" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (AlgEquiv.toAlgHom (LaurentPolynomial.invert (R := K)))))
local notation "p" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))

/-- The first conic puncture meets the actual global right branch with reciprocal parameter. -/
theorem terminalNodeZeroConicFirst_boundary :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₁)) ≫ i ≫ C ≫ g =
      ι ≫ PolygonNodeBranches.right K ≫ G := by
  rw [← terminalNodeZeroConicCoordinates_chart hπ data D j hj hk0 hk hp, ← Category.assoc,
    residueNodeConicFirst_spec, Category.assoc]

/-- The second conic puncture meets the actual global left branch with reciprocal parameter. -/
theorem terminalNodeZeroConicSecond_boundary :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₂)) ≫ i ≫ C ≫ g =
      ι ≫ PolygonNodeBranches.left K ≫ G := by
  rw [← terminalNodeZeroConicCoordinates_chart hπ data D j hj hk0 hk hp, ← Category.assoc,
    residueNodeConicSecond_spec, Category.assoc]

/-- The first original rational parameter is the inverted right branch globally. -/
theorem terminalNodeZeroConicFirst_parameter :
    p ≫ (conicFirstParameterIso (WeierstrassCurve.a₁ W₀) c ha).inv ≫
      conicFirstOpenImmersion (WeierstrassCurve.a₁ W₀) c ≫ C ≫ g =
        ι ≫ PolygonNodeBranches.right K ≫ G := by
  have H : Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₁)) ≫ i =
      Spec.map (CommRingCat.ofHom (conicPuncturedFirst W₀ c hc).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact conicBoundaryFirst_base W₀ c ha hc
  calc _ = Spec.map (CommRingCat.ofHom (conicPuncturedFirst W₀ c hc).toRingHom) ≫ C ≫ g := by
        rw [conicPuncturedFirst_spec c hc W₀ ha]
        simp only [Category.assoc]
    _ = _ := by
      rw [← H, Category.assoc]
      exact terminalNodeZeroConicFirst_boundary hπ data D j hj hk0 hk hp

/-- The second original rational parameter is the inverted left branch globally. -/
theorem terminalNodeZeroConicSecond_parameter :
    p ≫ (conicSecondParameterIso (WeierstrassCurve.a₁ W₀) c ha).inv ≫
      conicSecondOpenImmersion (WeierstrassCurve.a₁ W₀) c ≫ C ≫ g =
        ι ≫ PolygonNodeBranches.left K ≫ G := by
  have H : Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₂)) ≫ i =
      Spec.map (CommRingCat.ofHom (conicPuncturedSecond W₀ c hc).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact conicBoundarySecond_base W₀ c ha hc
  calc _ = Spec.map (CommRingCat.ofHom (conicPuncturedSecond W₀ c hc).toRingHom) ≫ C ≫ g := by
        rw [conicPuncturedSecond_spec c hc W₀ ha]
        simp only [Category.assoc]
    _ = _ := by
      rw [← H, Category.assoc]
      exact terminalNodeZeroConicSecond_boundary hπ data D j hj hk0 hk hp

end FLT.Mazur.WeierstrassDividedDepth

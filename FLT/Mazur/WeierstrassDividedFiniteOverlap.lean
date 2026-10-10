/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedBoundaryNormalization
public import FLT.Mazur.WeierstrassDividedFiniteTensorCharts

/-!
# The full integral overlap inside the finite model

The final divided chart and newest successive chart agree on their actual
principal opens, using the same depth transition that is tensor-base-changed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n)
open WeierstrassSuccessiveX
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "F" => finiteExterior hπ data E₀ (j + 1) hj

/-- The actual newest integral atlas map retains the prescribed boundary attachment. -/
@[reassoc] theorem finiteSuccessive_boundary :
    nextToX e ≫ finiteAtlasMap hπ data E₀ (j + 1) hj 1 =
      boundaryInclusion e ≫ (Exterior.dividedChart F) := by
  change nextToX e ≫
    ((finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).newX hπ e ≫
      (Exterior.exteriorChart F)) = _
  rw [← Category.assoc]
  exact Exterior.overlap F

/-- The original depth overlap commutes inside the whole finite integral model. -/
@[reassoc] theorem finiteSuccessive_depthOverlap :
    Spec.map (CommRingCat.ofHom
      (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e)).toRingHom) ≫
        boundaryInclusion e ≫ (Exterior.dividedChart F) =
      xOpenInclusion W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) ≫
        finiteAtlasMap hπ data E₀ (j + 1) hj 1 := by
  rw [← finiteSuccessive_boundary, depthOverlap_nextToX_assoc]

end FLT.Mazur.WeierstrassDividedDepth

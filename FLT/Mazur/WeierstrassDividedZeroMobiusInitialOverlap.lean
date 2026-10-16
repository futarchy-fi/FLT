/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroMobiusPolygonBoundary
public import FLT.Mazur.WeierstrassModificationXZeroMobiusOverlapBoundary

/-!
# The original full initial overlap commutes at both polygon labels

The two actual restrictions of the original initial-node intersection have
reciprocal fractional parameters. After the original opposite branch swap,
the polygon gluing identifies them at their original adjacent labels.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (k : ℕ)
local instance zeroMobiusOverlap_nilpotent : Fact (IsNilpotent (0 : R)) := ⟨1, by simp⟩

/-- The original adjacent initial labels identify inverse right-branch parameters. -/
@[reassoc] theorem initialPolygonLabel_opposite_boundary :
    (edgeInversion R).hom ≫ rightBranchOpen R 0 ≫ (branchSwapIso R 0).hom ≫
      PolygonInfinitesimal.chart R 0 (2 * k + 3) (by omega) (initialPolygonIndex k true) =
        rightBranchOpen R 0 ≫
          PolygonInfinitesimal.chart R 0 (2 * k + 3) (by omega)
            (initialPolygonIndex k false) := by
  rw [rightBranchOpen_branchSwapIso_assoc, PolygonInfinitesimal.overlap,
    initialPolygonIndex_preceding]
  simp only [precedingBranch, ← Category.assoc]
  rw [show (edgeInversion R).hom ≫ (edgeInversion R).hom = 𝟙 _ from
    (edgeInversion R).hom_inv_id, Category.id_comp]

variable (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)

include hbot in
/-- Both actual original initial overlap restrictions agree in the complete zero polygon. -/
@[reassoc] theorem zeroInitialMobiusPolygonMap_original_overlap :
    polynomialNodeOverlapInclusion W 0 ≫ zeroInitialMobiusPolygonMap W ha k false =
      polynomialNodeOverlapOpposite W 0 b3 b4 b6 r hr I hI hrI h3 ≫
        zeroInitialMobiusPolygonMap W ha k true := by
  simp only [zeroInitialMobiusPolygonMap, Bool.false_eq_true, ↓reduceIte, Category.id_comp]
  rw [zeroInitialMobiusChart_overlap_first_assoc W ha b3 b4 b6 r hr I hI hrI h3 hbot,
    zeroInitialMobiusChart_overlap_opposite_assoc W ha b3 b4 b6 r hr I hI hrI h3 hbot]
  rw [initialPolygonLabel_opposite_boundary]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSmoothTerminalCoefficientAction
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientOverAction

/-!
# The relative coefficient action on the original terminal tensor point

The independent input and genuine output define relative points of the final
coefficient model. Their proved point action is its actual relative action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => WeierstrassDilatation.ScalarExtension W (π ^ (start + (s + 1)))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "g" => globalDividedTensorChart hπ data K (s + 1) hs
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap K C))
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)

/-- Every point of the terminal tensor algebra retains the residue coefficient structure. -/
theorem terminalHorizontalTensorPoint_structure (f : A →ₐ[K] C) :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g) ≫ p = c := by
  rw [Category.assoc, globalDividedTensorChart_structure,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext f.commutes

/-- The original terminal tensor point as a relative point of the final coefficient model. -/
def terminalHorizontalTensorOverPoint (f : A →ₐ[K] C) : Over.mk c ⟶ Over.mk p :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g)
    (terminalHorizontalTensorPoint_structure hπ data D s hs f)

variable (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "V" => W.map (algebraMap R K)
local notation "a" => smoothHorizontalResiduePoint D (by omega)
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs K

/-- The genuine terminal output is the relative coefficient action on the original input. -/
theorem terminalHorizontalTensorOutput_over :
    lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X) a
      (smoothHorizontalResiduePoint_structure D (by omega)))
      (terminalHorizontalTensorOverPoint hπ data D s hs
        (smoothDividedTerminalTensorInput D d (by omega) (by omega) (by omega))) ≫ B =
      terminalHorizontalTensorOverPoint hπ data D s hs
        (smoothDividedTerminalTensorOutput D d (by omega) (by omega) (by omega)) := by
  rw [finiteGlobalCoefficientOverAction_points]
  apply Over.OverMorphism.ext
  exact smoothTerminalResidue_coefficientPointAction hπ data (s + 1) hs D
    (by omega) (by omega) (by omega)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteResidueNodes
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeMaps

/-!
# Explicit ordered node contractions under the finite atlas embeddings

The two actual finite node charts contract through the preceding integral
divided chart by the functions (u,0) and (u,-a₁*u), with its actual parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "N" => MiddleNodeOpen (residue R (Data.b6 e))
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ (start + j))
  (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
local notation "f" => tensorPreviousMap W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "F" => residueFirstNodeMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "G" => residueSecondNodeMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The first finite node's map on every function of the preceding integral chart. -/
def finiteFirstNodeContraction : A →ₐ[R] N :=
  (AlgHom.restrictScalars R F).comp (AlgHom.comp f (AlgEquiv.toAlgHom p))

/-- The opposite node's full map on the same preceding integral chart. -/
def finiteSecondNodeContraction : A →ₐ[R] N :=
  (AlgHom.restrictScalars R G).comp (AlgHom.comp f (AlgEquiv.toAlgHom p))

/-- The first finite node retains the original horizontal coordinate as u. -/
theorem finiteFirstNodeContraction_x :
    finiteFirstNodeContraction hπ data D j hj hk0 hk
      (WeierstrassDilatation.x W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)) =
        middleNodeU (residue R (Data.b6 e)) := by
  change F (f (p _)) = _
  rw [WeierstrassDilatation.parameterEquiv_x, tensorPreviousMap_x, residueFirstNodeMap_coord]
  rfl

/-- The first finite node retains the zero-slope tangent contraction. -/
theorem finiteFirstNodeContraction_y :
    finiteFirstNodeContraction hπ data D j hj hk0 hk
      (WeierstrassDilatation.y W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)) = 0 := by
  change F (f (p _)) = _
  rw [WeierstrassDilatation.parameterEquiv_y]
  exact residueFirstNode_previous_y D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The opposite finite node retains the same original horizontal coordinate. -/
theorem finiteSecondNodeContraction_x :
    finiteSecondNodeContraction hπ data D j hj hk0 hk
      (WeierstrassDilatation.x W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)) =
        middleNodeU (residue R (Data.b6 e)) := by
  change G (f (p _)) = _
  rw [WeierstrassDilatation.parameterEquiv_x, tensorPreviousMap_x, residueSecondNodeMap_coord]
  rfl

/-- The opposite finite node retains the original tangent slope -a₁. -/
theorem finiteSecondNodeContraction_y :
    finiteSecondNodeContraction hπ data D j hj hk0 hk
      (WeierstrassDilatation.y W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)) =
        -algebraMap K N (residue R W.a₁) * middleNodeU (residue R (Data.b6 e)) := by
  change G (f (p _)) = _
  rw [WeierstrassDilatation.parameterEquiv_y]
  exact residueSecondNode_previous_y D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The actual first finite atlas embedding has the displayed full contraction. -/
@[reassoc] theorem finiteResidueFirstNode_toCurve :
    finiteResidueFirstNode hπ data D j hj hk0 hk ≫
      pullback.snd q (finiteStructure hπ data (j + 1) hj) ≫
        finiteToCurve hπ data (j + 1) hj =
      Spec.map (CommRingCat.ofHom
        (finiteFirstNodeContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [finiteResidueFirstNode, Category.assoc, finiteSuccessiveTensorChart_toCurve,
    residueMiddleFirstNodeChart_eq_spec, xContraction]
  change Spec.map _ ≫ Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) ≫ _ = _
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The actual opposite finite atlas embedding has the displayed full contraction. -/
@[reassoc] theorem finiteResidueSecondNode_toCurve :
    finiteResidueSecondNode hπ data D j hj hk0 hk ≫
      pullback.snd q (finiteStructure hπ data (j + 1) hj) ≫
        finiteToCurve hπ data (j + 1) hj =
      Spec.map (CommRingCat.ofHom
        (finiteSecondNodeContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [finiteResidueSecondNode, Category.assoc, finiteSuccessiveTensorChart_toCurve,
    residueMiddleSecondNodeChart_eq_spec, xContraction]
  change Spec.map _ ≫ Spec.map _ ≫ (Spec.map _ ≫ Spec.map _) ≫ _ = _
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

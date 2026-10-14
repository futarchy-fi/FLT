/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteCoefficientPointSection
public import FLT.Mazur.EllipticFiniteDividedPointSection
public import FLT.Mazur.WeierstrassDividedTensorPointAction

/-!
# Actual divided coordinates of unrestricted specialization

The tensor evaluation of an original primitive nodal point is its unique
proper extension after coefficient restriction. Thus the actual residue
specialization factors through the named divided chart at that point's depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
  (S : Type u) [CommRing S] [Algebra A S]
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "C" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "f" => finiteGlobalStructure hπ data j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A S))

/-- Coefficient evaluation of the same original primitive coordinates. -/
def finiteNodeCoefficientEvaluation : C →ₐ[A] S :=
  (IsScalarTower.toAlgHom A A S).comp (finiteNodePointEvaluation A hπ data j hj P v hv)

/-- Its actual spectrum map is the coefficient restriction of the original evaluation. -/
theorem finiteNodeCoefficientEvaluation_spec :
    Spec.map (CommRingCat.ofHom
        (finiteNodeCoefficientEvaluation A hπ data j hj P v hv S).toRingHom) =
      q ≫ Spec.map
        (CommRingCat.ofHom (finiteNodePointEvaluation A hπ data j hj P v hv).toRingHom) := by
  rw [← Spec.map_comp]
  rfl

/-- The tensor evaluation computes the actual coefficient point of the original proper section. -/
theorem finiteCoefficientPointSection_nodeChart :
    dividedGlobalTensorAlgebraPoint hπ data j hj S S
        (finiteNodeCoefficientEvaluation A hπ data j hj P v hv S) =
      finiteCoefficientPointSection A hπ data j hj S P := by
  apply pullback.hom_ext
  · rw [dividedGlobalTensorAlgebraPoint_structure, finiteCoefficientPointSection_structure]
    exact Spec.map_id _
  · rw [dividedGlobalTensorAlgebraPoint_projection, finiteNodeCoefficientEvaluation_spec,
      Category.assoc, finitePointSection_nodeChart, finiteCoefficientPointSection_projection]

omit S [CommRing S] [Algebra A S] in
/-- The closed specialization is the actual residue evaluation on the indexed divided chart. -/
theorem finitePointSpecialization_nodeChart :
    dividedGlobalTensorAlgebraPoint hπ data j hj (ResidueField A) (ResidueField A)
        (finiteNodeCoefficientEvaluation A hπ data j hj P v hv (ResidueField A)) =
      finitePointSpecialization A hπ data j hj P :=
  finiteCoefficientPointSection_nodeChart A hπ data j hj P v hv (ResidueField A)

include v hv in
/-- Every specialized point is in the actual divided chart at its primitive coordinate depth. -/
theorem finiteCoefficientPointSection_mem_dividedChart (x : Spec (.of S)) :
    finiteCoefficientPointSection A hπ data j hj S P x ∈
      Set.range (globalDividedTensorChart hπ data S j hj) := by
  rw [← finiteCoefficientPointSection_nodeChart A hπ data j hj P v hv S]
  exact ⟨_, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth

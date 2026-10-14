/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteMiddleSpecialization
public import FLT.Mazur.WeierstrassDilatationTerminalSectionBranches

/-!
# Smooth odd-terminal specialization on the actual finite model

Every integral section of the final odd divided chart specializes to one of
its two actual punctured branches. For original primitive points this is the
unrestricted proper specialization, not a replacement reduction map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j) ≤ depth)
  (hp : 2 * (start + j) < depth) (ho : depth = 2 * (start + j) + 1)
local notation "k" => ResidueField A
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "C" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A k))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data j hj)
local notation "c" => terminalNodeChart hπ data D j hj hk0 hk hp

/-- The normalized node coordinates of an arbitrary actual integral terminal section. -/
def finiteOddNodePoint (f : C →ₐ[A] A) : Spec (.of k) ⟶ PolygonNodeBranches.node k :=
  Spec.map (CommRingCat.ofHom (WeierstrassDilatation.sectionNodeEvaluation D
    (start + j) hk0 hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp f).toRingHom)

/-- Its inclusion is the actual tensor specialization of the same integral section. -/
@[reassoc] theorem finiteOddNodePoint_inclusion (f : C →ₐ[A] A) :
    finiteOddNodePoint A data D j hj hk0 hk hp f ≫ c =
      dividedGlobalTensorAlgebraPoint hπ data j hj k k
        ((IsScalarTower.toAlgHom A A k).comp f) := by
  rw [finiteOddNodePoint, terminalNodeChart, ← Category.assoc,
    WeierstrassDilatation.sectionNodeEvaluation_inclusion]
  rfl

include D hk0 hk hp ho in
/-- Odd-terminal integral sections land on one of the two full punctured branches. -/
theorem finiteOddNodePoint_mem_branches (f : C →ₐ[A] A) (x : Spec (.of k)) :
    finiteOddNodePoint A data D j hj hk0 hk hp f x ∈
      Set.range (PolygonNodeBranches.left k) ∪ Set.range (PolygonNodeBranches.right k) :=
  WeierstrassDilatation.sectionNodeEvaluation_mem_branches D (start + j) hk0 hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp ho f x

include D hk0 hk hp ho in
/-- The actual closed model is smooth at every odd-terminal integral section. -/
theorem finiteOddSection_specialization_smooth (f : C →ₐ[A] A) (x : Spec (.of k)) :
    let _ := finitePointSpecializationStructure_lfp A hπ data j hj
    dividedGlobalTensorAlgebraPoint hπ data j hj k k
      ((IsScalarTower.toAlgHom A A k).comp f) x ∈ (p).smoothLocus := by
  let _ := finitePointSpecializationStructure_lfp A hπ data j hj
  rw [← finiteOddNodePoint_inclusion A hπ data D j hj hk0 hk hp f]
  rcases finiteOddNodePoint_mem_branches A data D j hj hk0 hk hp ho f x with
    ⟨y, hy⟩ | ⟨y, hy⟩
  · change c (finiteOddNodePoint A data D j hj hk0 hk hp f x) ∈ _
    rw [← hy]
    apply (PolygonAtlas.mem_smooth_iff (PolygonNodeBranches.left k ≫ c) p y).mpr
    have hs : Smooth ((PolygonNodeBranches.left k ≫ c) ≫ p) := by
      rw [Category.assoc, terminalNodeChart_structure]
      infer_instance
    let _ := hs
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  · change c (finiteOddNodePoint A data D j hj hk0 hk hp f x) ∈ _
    rw [← hy]
    apply (PolygonAtlas.mem_smooth_iff (PolygonNodeBranches.right k ≫ c) p y).mpr
    have hs : Smooth ((PolygonNodeBranches.right k ≫ c) ≫ p) := by
      rw [Category.assoc, terminalNodeChart_structure]
      infer_instance
    let _ := hs
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial

include D hk0 hk hp ho in
/-- Original points at final odd depth have smooth unrestricted proper specialization. -/
theorem finitePointSpecialization_odd_smooth
    (P : (W.map (algebraMap A K)).toProjective.Point)
    (v : NodePointCoordinates A W π P) (hv : v.depth = start + j) (x : Spec (.of k)) :
    let _ := finitePointSpecializationStructure_lfp A hπ data j hj
    finitePointSpecialization A hπ data j hj P x ∈ (p).smoothLocus := by
  rw [← finitePointSpecialization_nodeChart A hπ data j hj P v hv]
  exact finiteOddSection_specialization_smooth A hπ data D j hj hk0 hk hp ho
    (finiteNodePointEvaluation A hπ data j hj P v hv) x

end FLT.Mazur.WeierstrassDividedDepth

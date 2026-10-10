/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalResidueNodes
public import FLT.Mazur.WeierstrassDividedOlderZeroExtendedSections
public import FLT.Mazur.WeierstrassSuccessiveXResidueIncidencePoints

/-!
# Ordered positive-depth incidence sections in the global model

Both middle-node origins define sections of the actual retained residue model.
They keep the original tensor tangent order and remain distinct at every stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "o" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (middleNodeOrigin c)))
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (j + 1 + r) hr
local notation "first" => residueFirstIncidencePoint D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "second" => residueSecondIncidencePoint D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The original first ordered tensor point in the retained global model. -/
def olderGlobalFirstSection :=
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom first)) ≫ g

/-- The original opposite ordered tensor point in the retained global model. -/
def olderGlobalSecondSection :=
  Spec.map (CommRingCat.ofHom (AlgHom.toRingHom second)) ≫ g

/-- The first full middle-node origin gives exactly the first global point. -/
@[reassoc] theorem olderGlobalFirstNode_origin :
    o ≫ olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk =
      olderGlobalFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalResidueFirstNode, olderResidueFirstNode, ← Category.assoc,
    ← Category.assoc, residueMiddleFirstNodeChart_origin]
  rfl

/-- The opposite full middle-node origin gives the second global point. -/
@[reassoc] theorem olderGlobalSecondNode_origin :
    o ≫ olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk =
      olderGlobalSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalResidueSecondNode, olderResidueSecondNode, ← Category.assoc,
    ← Category.assoc, residueMiddleSecondNodeChart_origin]
  rfl

/-- The first ordered point is an actual section of the residue structure. -/
@[reassoc] theorem olderGlobalFirstSection_structure :
    olderGlobalFirstSection hπ data D j hj r hr hk0 hk ≫ pullback.fst q f =
      𝟙 (Spec (.of K)) := by
  rw [olderGlobalFirstSection, Category.assoc, olderGlobalTensorChart_structure]
  exact residueAlgebraPoint_structure _

/-- The opposite ordered point is an actual section of that same structure. -/
@[reassoc] theorem olderGlobalSecondSection_structure :
    olderGlobalSecondSection hπ data D j hj r hr hk0 hk ≫ pullback.fst q f =
      𝟙 (Spec (.of K)) := by
  rw [olderGlobalSecondSection, Category.assoc, olderGlobalTensorChart_structure]
  exact residueAlgebraPoint_structure _

/-- Every nonzero coefficient extension retains distinct ordered global points. -/
theorem olderGlobalSections_extension_ne (S : Type u) [CommRing S] [Nontrivial S]
    [Algebra K S] :
    Spec.map (CommRingCat.ofHom (algebraMap K S)) ≫
        olderGlobalFirstSection hπ data D j hj r hr hk0 hk ≠
      Spec.map (CommRingCat.ofHom (algebraMap K S)) ≫
        olderGlobalSecondSection hπ data D j hj r hr hk0 hk := by
  intro h
  rw [olderGlobalFirstSection, olderGlobalSecondSection,
    ← Category.assoc, ← Category.assoc] at h
  exact residueIncidencePoints_extension_ne D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) S
    ((cancel_mono g).mp h)

/-- Retention never identifies the two original middle-node sections. -/
theorem olderGlobalSections_ne :
    olderGlobalFirstSection hπ data D j hj r hr hk0 hk ≠
      olderGlobalSecondSection hπ data D j hj r hr hk0 hk := by
  intro h
  exact olderGlobalSections_extension_ne hπ data D j hj r hr hk0 hk K
    (congrArg (fun t => Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ t) h)

end FLT.Mazur.WeierstrassDividedDepth

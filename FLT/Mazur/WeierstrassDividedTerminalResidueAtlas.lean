/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalResidueCharts

/-!
# Complete global covers with the terminal chart normalized by parity

Replacing precisely the terminal atlas object by its full Laurent or node
normal form leaves a cover of the entire projective residue model. Infinity
and every original exterior index, including the initial chart, remain present.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j) ≤ depth)
local notation "K" => ResidueField R
local notation "A" => globalTensorAtlasObject hπ data K j hj
local notation "f" => globalTensorAtlasMap hπ data K j hj

section Laurent
variable (hp : 2 * (start + j) = depth)

/-- The complete indexed global atlas with the whole terminal laurent normal form. -/
def terminalLaurentAtlasObject : Fin (j + 3) → Scheme :=
  Fin.cases (A 0) (Fin.cases (Spec (.of (K[T;T⁻¹]))) (fun i => A i.succ.succ))

/-- The parity normalization identifies each object with its original global atlas index. -/
def terminalLaurentAtlasObjectIso (i : Fin (j + 3)) :
    terminalLaurentAtlasObject hπ data j hj i ≅ A i :=
  Fin.cases (Iso.refl _)
    (Fin.cases (terminalLaurentAtlasIso hπ data D j hj hk0 hk hp) (fun _ => Iso.refl _)) i

/-- Every normalized or retained object has its actual map to the projective residue model. -/
def terminalLaurentAtlasMap (i : Fin (j + 3)) :
    terminalLaurentAtlasObject hπ data j hj i ⟶ finiteGlobalTensorModel hπ data K j hj :=
  (terminalLaurentAtlasObjectIso hπ data D j hj hk0 hk hp i).hom ≫ f i

/-- The normalized terminal atlas covers the entire global residue model. -/
def terminalLaurentOpenCover : (finiteGlobalTensorModel hπ data K j hj).OpenCover :=
  (globalTensorOpenCover hπ data K j hj).copy (Fin (j + 3))
    (terminalLaurentAtlasObject hπ data j hj)
    (terminalLaurentAtlasMap hπ data D j hj hk0 hk hp) (Equiv.refl _)
    (terminalLaurentAtlasObjectIso hπ data D j hj hk0 hk hp) (fun _ => rfl)

/-- The terminal member of the complete cover is the original normalized chart map. -/
theorem terminalLaurentAtlasMap_terminal :
    terminalLaurentAtlasMap hπ data D j hj hk0 hk hp (Fin.succ 0) =
      terminalLaurentChart hπ data D j hj hk0 hk hp :=
  terminalLaurentAtlasIso_map hπ data D j hj hk0 hk hp

/-- Infinity retains precisely its original map in the complete normalized cover. -/
theorem terminalLaurentAtlasMap_infinity :
    terminalLaurentAtlasMap hπ data D j hj hk0 hk hp 0 =
      finiteInfinityTensorChart hπ data K j hj := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Every exterior retains its exact original index and map, including the initial chart. -/
theorem terminalLaurentAtlasMap_exterior (i : Fin (j + 1)) :
    terminalLaurentAtlasMap hπ data D j hj hk0 hk hp i.succ.succ = f i.succ.succ := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _
end Laurent

section Node
variable (hp : 2 * (start + j) < depth)

/-- The complete indexed global atlas with the whole terminal node normal form. -/
def terminalNodeAtlasObject : Fin (j + 3) → Scheme :=
  Fin.cases (A 0) (Fin.cases (PolygonNodeBranches.node K) (fun i => A i.succ.succ))

/-- The parity normalization identifies each object with its original global atlas index. -/
def terminalNodeAtlasObjectIso (i : Fin (j + 3)) :
    terminalNodeAtlasObject hπ data j hj i ≅ A i :=
  Fin.cases (Iso.refl _)
    (Fin.cases (terminalNodeAtlasIso hπ data D j hj hk0 hk hp) (fun _ => Iso.refl _)) i

/-- Every normalized or retained object has its actual map to the projective residue model. -/
def terminalNodeAtlasMap (i : Fin (j + 3)) :
    terminalNodeAtlasObject hπ data j hj i ⟶ finiteGlobalTensorModel hπ data K j hj :=
  (terminalNodeAtlasObjectIso hπ data D j hj hk0 hk hp i).hom ≫ f i

/-- The normalized terminal atlas covers the entire global residue model. -/
def terminalNodeOpenCover : (finiteGlobalTensorModel hπ data K j hj).OpenCover :=
  (globalTensorOpenCover hπ data K j hj).copy (Fin (j + 3))
    (terminalNodeAtlasObject hπ data j hj)
    (terminalNodeAtlasMap hπ data D j hj hk0 hk hp) (Equiv.refl _)
    (terminalNodeAtlasObjectIso hπ data D j hj hk0 hk hp) (fun _ => rfl)

/-- The terminal member of the complete cover is the original normalized chart map. -/
theorem terminalNodeAtlasMap_terminal :
    terminalNodeAtlasMap hπ data D j hj hk0 hk hp (Fin.succ 0) =
      terminalNodeChart hπ data D j hj hk0 hk hp :=
  terminalNodeAtlasIso_map hπ data D j hj hk0 hk hp

/-- Infinity retains precisely its original map in the complete normalized cover. -/
theorem terminalNodeAtlasMap_infinity :
    terminalNodeAtlasMap hπ data D j hj hk0 hk hp 0 =
      finiteInfinityTensorChart hπ data K j hj := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Every exterior retains its exact original index and map, including the initial chart. -/
theorem terminalNodeAtlasMap_exterior (i : Fin (j + 1)) :
    terminalNodeAtlasMap hπ data D j hj hk0 hk hp i.succ.succ = f i.succ.succ := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _
end Node

end FLT.Mazur.WeierstrassDividedDepth

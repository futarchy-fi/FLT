/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherAtlas
public import FLT.Mazur.WeierstrassDividedFifthDeepAtlasIdentification

/-!
# Actual labels of the two unchanged paired fifth factors

Every installed node is identified with its full fifth smoothing. Its whole-node
comparison recovers exactly the previous fourth-atlas inclusion at that label.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFifthDeepNodeIso arithmeticFifthDeepEarlierIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (ha₃ : 3 = j)
local notation "Q" => Quotient R π m
local notation "A" => arithmeticFifthFartherAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFifthFartherAtlasCorrection hπ data H m j hj u hu ha₃
local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha₃
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "s" => fun v ↦ arithmeticFifthDeepSmoothing hπ data H j hj u hu v m
local notation "N" => arithmeticFifthDeepNodeIso hπ data H j hj u hu m

variable (v : FifthDeepNode) (hv : v ≠ .farther) (a : ℕ) (ha : a + fifthDeepOffset v = j)
local notation "D" =>
  arithmeticFifthFartherInputIdentification hπ data H m j hj u hu (by omega) v a ha

/-- The installed paired label has its exact changed fifth smoothing. -/
def arithmeticFifthFartherNodeIdentification (b : Bool) :
    PolygonSmoothing.chart Q (s v b) ≅
      A (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b) := eqToIso (by
  cases v
  · change a + 1 = j at ha
    simp only [arithmeticFifthFartherAtlasObject, show ¬a = j by omega, ha, ↓reduceIte]
  · change a + 2 = j at ha
    simp only [arithmeticFifthFartherAtlasObject, show ¬a = j by omega,
      show ¬a + 1 = j by omega, ha, ↓reduceIte]
  · exact (hv rfl).elim)

local notation "F" => arithmeticFifthFartherNodeIdentification hπ data H m j hj u hu ha₃ v hv a ha

omit [IsBezout R] in
/-- The actual installed correction is the full paired node factor from its exact old source. -/
theorem arithmeticFifthFartherAtlasCorrection_node (b : Bool) :
    E (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b) = (D b).symm ≪≫ N v b ≪≫ F b := by
  cases v
  · change a + 1 = j at ha
    simp only [arithmeticFifthFartherAtlasCorrection, show ¬a = j by omega, ha, ↓reduceDIte]
    rfl
  · change a + 2 = j at ha
    simp only [arithmeticFifthFartherAtlasCorrection, show ¬a = j by omega,
      show ¬a + 1 = j by omega, ha, ↓reduceDIte]
    rfl
  · exact (hv rfl).elim

/-- The installed full node comparison recovers its exact fourth global inclusion. -/
@[reassoc] theorem arithmeticFifthFartherNode_chart (b : Bool) :
    (N v b).hom ≫ (F b).hom ≫ ι (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b) =
      (D b).hom ≫ κ (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b) := by
  have h := arithmeticFifthFartherAtlasCorrection_chart hπ data H m j hj u hu ha₃
    (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b)
  rw [arithmeticFifthFartherAtlasCorrection_node hπ data H m j hj u hu ha₃ v hv a ha b] at h
  have hh := congrArg (fun f ↦ (D b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherNodeIdentification
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasSystem
public import FLT.Mazur.WeierstrassDividedFifthFartherInputRestriction

/-!
# Concrete restrictions at the installed fifth paired nodes

The global atlas arrows are the actual coefficient quotients of the complete
fifth smoothings, at both unchanged paired nodes at depth three.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthFartherAtlasCorrection arithmeticFifthDeepNodeIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (ha₃ : 3 = j) (m : ℕ) (v : FifthDeepNode) (hv : v ≠ .farther)
  (a : ℕ) (ha : a + fifthDeepOffset v = j)
local notation "S" => arithmeticFifthFartherAtlasRestriction hπ data H j hj u hu ha₃
local notation "N" => fun k ↦
  arithmeticFifthFartherNodeIdentification hπ data H k j hj u hu ha₃ v hv a ha
local notation "D" => fun k ↦
  arithmeticFifthFartherInputIdentification hπ data H k j hj u hu (by omega) v a ha
local notation "C" => fun k ↦ arithmeticFifthDeepNodeIso hπ data H j hj u hu k v

omit [IsBezout R] in
/-- Every installed full fifth node has its explicit changing-smoothing quotient square. -/
@[reassoc] theorem arithmeticFifthFartherNodeIdentification_restriction (b : Bool) :
    (N m b).hom ≫ S m (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b) =
      arithmeticFifthDeepNodeRestriction hπ data H j hj u hu m v b ≫ (N (m + 1) b).hom := by
  have h := arithmeticFifthFartherAtlasCorrection_restriction hπ data H j hj u hu ha₃ m
    (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b)
  dsimp only at h
  rw [arithmeticFifthFartherAtlasCorrection_node hπ data H m j hj u hu ha₃ v hv a ha b,
    arithmeticFifthFartherAtlasCorrection_node hπ data H (m + 1) j hj u hu ha₃ v hv a ha b] at h
  have hh := congrArg (fun f ↦ (D m b).hom ≫ f) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] at hh
  rw [arithmeticFifthFartherInputIdentification_restriction_assoc, Iso.hom_inv_id_assoc] at hh
  apply (cancel_epi (C m b).hom).mp
  rw [← arithmeticFifthDeepNodeIso_restriction_assoc]
  exact hh

/-- The concrete paired coefficient maps commute with the full global arithmetic quotient. -/
@[reassoc] theorem arithmeticFifthFartherInstalledNodeChart_restriction (b : Bool) :
    arithmeticFifthDeepNodeRestriction hπ data H j hj u hu m v b ≫
        (N (m + 1) b).hom ≫ arithmeticFifthFartherAtlasChart hπ data H (m + 1) j hj u hu ha₃
          (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b) =
      (N m b).hom ≫ arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha₃
          (.retained ⟨a, by have := fifthDeepOffset_pos v; omega⟩ b) ≫
        simultaneousTwistedArithmeticRestriction hπ data H m j hj u hu := by
  rw [← arithmeticFifthFartherNodeIdentification_restriction_assoc,
    arithmeticFifthFartherAtlasChart_restriction]

end FLT.Mazur.WeierstrassDividedDepth

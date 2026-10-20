/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleTangentGluing
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition

/-!
# Promote the exact-triple tangent law to a common finite model

The constructed tangent branch union moves to any supplied later stage.
Its complete cubic formula, local restrictions and coefficient map are unchanged.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus
local notation "tan" => dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6
local notation "inc" => tripleTangentNeighborhoodInclusion D data hk a c
local notation "opens" => fun i : Bool => (inc i).opensRange

local notation "O" => tripleTangentBranchOutputOpen D data hk a c
local notation "e" => IsScalarTower.toAlgHom R S T
variable (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "Q" => (base).smoothLocus
local notation "promote" => finiteGlobalSmoothTransition hπ data k j hkj hj

/-- The entire constructed exact-triple tangent law in a later common finite model. -/
def triplePromotedTangentOutput : (O).toScheme ⟶ (Q).toScheme :=
  tripleTangentGluedOutput D data hk a c ≫ promote

/-- Promotion retains the complete original cubic tangent formula. -/
@[reassoc] theorem triplePromotedTangentOutput_contraction :
    triplePromotedTangentOutput D data hk a c j hj hkj ≫ (Q).ι ≫
        finiteGlobalContraction hπ data j hj = (O).ι ≫ tan := by
  rw [triplePromotedTangentOutput, Category.assoc, finiteGlobalSmoothTransition_contraction,
    tripleTangentGluedOutput_contraction]

/-- The exact-triple output retains its original coefficient point. -/
@[reassoc] theorem triplePromotedTangentOutput_structure :
    triplePromotedTangentOutput D data hk a c j hj hkj ≫ (Q).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (Q).ι ≫ finiteGlobalContraction hπ data j hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [triplePromotedTangentOutput_contraction_assoc, dividedTangentToCurve_structure]

/-- Every original local formula is preserved in the chosen common target. -/
@[reassoc] theorem triplePromotedTangentOutput_restrict (i : Bool) :
    (Scheme.Opens.iSupOpenCover opens).f i ≫
          triplePromotedTangentOutput D data hk a c j hj hkj =
      tripleTangentLocalOutput D data hk a c i ≫ promote := by
  rw [triplePromotedTangentOutput, tripleTangentGluedOutput_restrict_assoc]

end FLT.Mazur.WeierstrassDividedDepth

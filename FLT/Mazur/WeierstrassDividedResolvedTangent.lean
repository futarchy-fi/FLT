/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTangentInput
public import FLT.Mazur.WeierstrassDividedResolvedSecant

/-!
# Resolved outputs on the new two-divided-input tangent domain

Pull the genuine divided tangent open back to two arbitrary resolved smooth
inputs. Where its constructed original output is smooth, it lifts to the
same finite model. Agreement with the previous partial addition and further
charts covering the remaining pairs are separate gluing obligations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "T" => WeierstrassDilatation.DividedPairTangentRing W s (d).b3 (d).b4 (d).b6
local notation "a" => WeierstrassDilatation.dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => WeierstrassDilatation.dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base

/-- Impose smoothness of both inputs on the genuine two-divided-input tangent domain. -/
def finiteResolvedTangentSource : Scheme :=
  pullback (finiteTangentInput hπ data j hj) (finiteResolvedPairInclusion hπ data j hj)

/-- This domain is an actual open inside the product of two full resolved smooth inputs. -/
def finiteResolvedTangentInput :
    finiteResolvedTangentSource hπ data j hj ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.snd _ _

instance finiteResolvedTangentInput_open :
    IsOpenImmersion (finiteResolvedTangentInput hπ data j hj) :=
  inferInstanceAs (IsOpenImmersion (pullback.snd _ _))

/-- The original cubic output on this domain is constructed by the divided tangent formula. -/
def finiteResolvedTangentOriginalOutput :
    finiteResolvedTangentSource hπ data j hj ⟶ integralCurve W :=
  pullback.fst (finiteTangentInput hπ data j hj) (finiteResolvedPairInclusion hπ data j hj) ≫
    WeierstrassDilatation.dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
      (d).factor3 (d).factor4 (d).factor6

/-- The constructed output shares the coefficient point of both resolved inputs. -/
@[reassoc] theorem finiteResolvedTangentOriginalOutput_structure :
    finiteResolvedTangentOriginalOutput hπ data j hj ≫ integralCurveStructure W =
      finiteResolvedTangentInput hπ data j hj ≫ pullback.fst t t ≫ t := by
  rw [finiteResolvedTangentOriginalOutput, Category.assoc,
    WeierstrassDilatation.dividedTangentToCurve_structure,
    ← finiteTangentInput_structure hπ data j hj, pullback.condition_assoc]
  simp only [finiteResolvedPairInclusion, finiteResolvedTangentInput, pullback.map,
    Category.assoc, pullback.lift_fst_assoc]

/-- The actual open where this new formula has an originally smooth output. -/
def finiteResolvedTangentOutputOpen : (finiteResolvedTangentSource hπ data j hj).Opens :=
  finiteResolvedTangentOriginalOutput hπ data j hj ⁻¹ᵁ integralSmoothOpen W

/-- The new local multiplication domain remains openly embedded in the full resolved product. -/
def finiteResolvedTangentDomainMap :
    (finiteResolvedTangentOutputOpen hπ data j hj).toScheme ⟶
      finiteResolvedProduct hπ data j hj :=
  (finiteResolvedTangentOutputOpen hπ data j hj).ι ≫ finiteResolvedTangentInput hπ data j hj

instance finiteResolvedTangentDomainMap_open :
    IsOpenImmersion (finiteResolvedTangentDomainMap hπ data j hj) := by
  unfold finiteResolvedTangentDomainMap
  infer_instance

/-- The actual originally smooth output on the new domain. -/
def finiteResolvedTangentOriginalSmooth :
    (finiteResolvedTangentOutputOpen hπ data j hj).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  finiteResolvedTangentOriginalOutput hπ data j hj ∣_ integralSmoothOpen W

/-- Lift the constructed output to the same entire resolved smooth locus. -/
def finiteResolvedTangentAddition :
    (finiteResolvedTangentOutputOpen hπ data j hj).toScheme ⟶ (U).toScheme :=
  finiteResolvedTangentOriginalSmooth hπ data j hj ≫ finiteOriginalToResolved hπ data j hj

/-- The resolved output contracts to exactly the new original tangent formula. -/
@[reassoc] theorem finiteResolvedTangentAddition_contraction :
    finiteResolvedTangentAddition hπ data j hj ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      (finiteResolvedTangentOutputOpen hπ data j hj).ι ≫
        finiteResolvedTangentOriginalOutput hπ data j hj := by
  rw [finiteResolvedTangentAddition, Category.assoc, finiteOriginalToResolved_inclusion_assoc,
    finiteGlobalSmoothEmbedding_contraction, finiteResolvedTangentOriginalSmooth]
  exact morphismRestrict_ι _ _

/-- The lift retains the original coefficient point of the constructed tangent output. -/
@[reassoc] theorem finiteResolvedTangentAddition_original_structure :
    finiteResolvedTangentAddition hπ data j hj ≫ (U).ι ≫ base =
      (finiteResolvedTangentOutputOpen hπ data j hj).ι ≫
        finiteResolvedTangentOriginalOutput hπ data j hj ≫ integralCurveStructure W := by
  exact finiteResolvedTangentAddition_contraction_assoc hπ data j hj (integralCurveStructure W)

/-- The local multiplication is over the same coefficient scheme as its two actual inputs. -/
@[reassoc] theorem finiteResolvedTangentAddition_structure :
    finiteResolvedTangentAddition hπ data j hj ≫ t =
      finiteResolvedTangentDomainMap hπ data j hj ≫ pullback.fst t t ≫ t := by
  rw [finiteResolvedTangentAddition_original_structure,
    finiteResolvedTangentOriginalOutput_structure]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

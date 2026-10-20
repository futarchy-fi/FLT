/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteReciprocalInput
public import FLT.Mazur.WeierstrassDividedResolvedSecant

/-!
# Resolved outputs on the new two-divided-input reciprocal domain

Pull the genuine divided reciprocal open back to two arbitrary resolved smooth
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
local notation "T" => WeierstrassDilatation.DividedPairReciprocalOutputRing W s (d).b3 (d).b4 (d).b6
local notation "a" => WeierstrassDilatation.dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => WeierstrassDilatation.dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base

/-- Impose smoothness of both inputs on the genuine two-divided-input reciprocal domain. -/
def finiteResolvedReciprocalSource : Scheme :=
  pullback (finiteReciprocalInput hπ data j hj) (finiteResolvedPairInclusion hπ data j hj)

/-- This domain is an actual open inside the product of two full resolved smooth inputs. -/
def finiteResolvedReciprocalInput :
    finiteResolvedReciprocalSource hπ data j hj ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.snd _ _

instance finiteResolvedReciprocalInput_open :
    IsOpenImmersion (finiteResolvedReciprocalInput hπ data j hj) :=
  inferInstanceAs (IsOpenImmersion (pullback.snd _ _))

/-- The original cubic output on this domain is constructed by the divided reciprocal formula. -/
def finiteResolvedReciprocalOriginalOutput :
    finiteResolvedReciprocalSource hπ data j hj ⟶ integralCurve W :=
  pullback.fst (finiteReciprocalInput hπ data j hj) (finiteResolvedPairInclusion hπ data j hj) ≫
    WeierstrassDilatation.dividedReciprocalToCurve W s (d).b3 (d).b4 (d).b6 a c
      (d).factor3 (d).factor4 (d).factor6

/-- The constructed output shares the coefficient point of both resolved inputs. -/
@[reassoc] theorem finiteResolvedReciprocalOriginalOutput_structure :
    finiteResolvedReciprocalOriginalOutput hπ data j hj ≫ integralCurveStructure W =
      finiteResolvedReciprocalInput hπ data j hj ≫ pullback.fst t t ≫ t := by
  rw [finiteResolvedReciprocalOriginalOutput, Category.assoc,
    WeierstrassDilatation.dividedReciprocalToCurve_structure,
    ← finiteReciprocalInput_structure hπ data j hj, pullback.condition_assoc]
  simp only [finiteResolvedPairInclusion, finiteResolvedReciprocalInput, pullback.map,
    Category.assoc, pullback.lift_fst_assoc]

/-- The actual open where this new formula has an originally smooth output. -/
def finiteResolvedReciprocalOutputOpen : (finiteResolvedReciprocalSource hπ data j hj).Opens :=
  finiteResolvedReciprocalOriginalOutput hπ data j hj ⁻¹ᵁ integralSmoothOpen W

/-- The new local multiplication domain remains openly embedded in the full resolved product. -/
def finiteResolvedReciprocalDomainMap :
    (finiteResolvedReciprocalOutputOpen hπ data j hj).toScheme ⟶
      finiteResolvedProduct hπ data j hj :=
  (finiteResolvedReciprocalOutputOpen hπ data j hj).ι ≫ finiteResolvedReciprocalInput hπ data j hj

instance finiteResolvedReciprocalDomainMap_open :
    IsOpenImmersion (finiteResolvedReciprocalDomainMap hπ data j hj) := by
  unfold finiteResolvedReciprocalDomainMap
  infer_instance

/-- The actual originally smooth output on the new domain. -/
def finiteResolvedReciprocalOriginalSmooth :
    (finiteResolvedReciprocalOutputOpen hπ data j hj).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  finiteResolvedReciprocalOriginalOutput hπ data j hj ∣_ integralSmoothOpen W

/-- Lift the constructed output to the same entire resolved smooth locus. -/
def finiteResolvedReciprocalAddition :
    (finiteResolvedReciprocalOutputOpen hπ data j hj).toScheme ⟶ (U).toScheme :=
  finiteResolvedReciprocalOriginalSmooth hπ data j hj ≫ finiteOriginalToResolved hπ data j hj

/-- The resolved output contracts to exactly the new original reciprocal formula. -/
@[reassoc] theorem finiteResolvedReciprocalAddition_contraction :
    finiteResolvedReciprocalAddition hπ data j hj ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      (finiteResolvedReciprocalOutputOpen hπ data j hj).ι ≫
        finiteResolvedReciprocalOriginalOutput hπ data j hj := by
  rw [finiteResolvedReciprocalAddition, Category.assoc, finiteOriginalToResolved_inclusion_assoc,
    finiteGlobalSmoothEmbedding_contraction, finiteResolvedReciprocalOriginalSmooth]
  exact morphismRestrict_ι _ _

/-- The lift retains the original coefficient point of the constructed reciprocal output. -/
@[reassoc] theorem finiteResolvedReciprocalAddition_original_structure :
    finiteResolvedReciprocalAddition hπ data j hj ≫ (U).ι ≫ base =
      (finiteResolvedReciprocalOutputOpen hπ data j hj).ι ≫
        finiteResolvedReciprocalOriginalOutput hπ data j hj ≫ integralCurveStructure W := by
  exact finiteResolvedReciprocalAddition_contraction_assoc hπ data j hj (integralCurveStructure W)

/-- The local multiplication is over the same coefficient scheme as its two actual inputs. -/
@[reassoc] theorem finiteResolvedReciprocalAddition_structure :
    finiteResolvedReciprocalAddition hπ data j hj ≫ t =
      finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.fst t t ≫ t := by
  rw [finiteResolvedReciprocalAddition_original_structure,
    finiteResolvedReciprocalOriginalOutput_structure]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

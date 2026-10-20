/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteSecantInput
public import FLT.Mazur.WeierstrassDividedResolvedProductOpens

/-!
# Resolved outputs on the new two-divided-input secant domain

Pull the genuine divided secant open back to two arbitrary resolved smooth
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
local notation "T" => WeierstrassDilatation.DividedPairSecantRing W s (d).b3 (d).b4 (d).b6
local notation "a" => WeierstrassDilatation.dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => WeierstrassDilatation.dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base

/-- The product of the two full resolved smooth loci embeds in the whole-model product. -/
def finiteResolvedPairInclusion : finiteResolvedProduct hπ data j hj ⟶ pullback base base :=
  pullback.map t t base base (U).ι (U).ι (𝟙 _) (by simp) (by simp)

instance finiteResolvedPairInclusion_open :
    IsOpenImmersion (finiteResolvedPairInclusion hπ data j hj) := by
  unfold finiteResolvedPairInclusion
  infer_instance

/-- Impose smoothness of both inputs on the genuine two-divided-input secant domain. -/
def finiteResolvedSecantSource : Scheme :=
  pullback (finiteSecantInput hπ data j hj) (finiteResolvedPairInclusion hπ data j hj)

/-- This domain is an actual open inside the product of two full resolved smooth inputs. -/
def finiteResolvedSecantInput :
    finiteResolvedSecantSource hπ data j hj ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.snd _ _

instance finiteResolvedSecantInput_open :
    IsOpenImmersion (finiteResolvedSecantInput hπ data j hj) :=
  inferInstanceAs (IsOpenImmersion (pullback.snd _ _))

/-- The original cubic output on this domain is constructed by the divided secant formula. -/
def finiteResolvedSecantOriginalOutput :
    finiteResolvedSecantSource hπ data j hj ⟶ integralCurve W :=
  pullback.fst (finiteSecantInput hπ data j hj) (finiteResolvedPairInclusion hπ data j hj) ≫
    WeierstrassDilatation.dividedSecantToCurve W s (d).b3 (d).b4 (d).b6 a c
      (d).factor3 (d).factor4 (d).factor6

/-- The constructed output shares the coefficient point of both resolved inputs. -/
@[reassoc] theorem finiteResolvedSecantOriginalOutput_structure :
    finiteResolvedSecantOriginalOutput hπ data j hj ≫ integralCurveStructure W =
      finiteResolvedSecantInput hπ data j hj ≫ pullback.fst t t ≫ t := by
  rw [finiteResolvedSecantOriginalOutput, Category.assoc,
    WeierstrassDilatation.dividedSecantToCurve_structure,
    ← finiteSecantInput_structure hπ data j hj, pullback.condition_assoc]
  simp only [finiteResolvedPairInclusion, finiteResolvedSecantInput, pullback.map,
    Category.assoc, pullback.lift_fst_assoc]

/-- The actual open where this new formula has an originally smooth output. -/
def finiteResolvedSecantOutputOpen : (finiteResolvedSecantSource hπ data j hj).Opens :=
  finiteResolvedSecantOriginalOutput hπ data j hj ⁻¹ᵁ integralSmoothOpen W

/-- The new local multiplication domain remains openly embedded in the full resolved product. -/
def finiteResolvedSecantDomainMap :
    (finiteResolvedSecantOutputOpen hπ data j hj).toScheme ⟶
      finiteResolvedProduct hπ data j hj :=
  (finiteResolvedSecantOutputOpen hπ data j hj).ι ≫ finiteResolvedSecantInput hπ data j hj

instance finiteResolvedSecantDomainMap_open :
    IsOpenImmersion (finiteResolvedSecantDomainMap hπ data j hj) := by
  unfold finiteResolvedSecantDomainMap
  infer_instance

/-- The actual originally smooth output on the new domain. -/
def finiteResolvedSecantOriginalSmooth :
    (finiteResolvedSecantOutputOpen hπ data j hj).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  finiteResolvedSecantOriginalOutput hπ data j hj ∣_ integralSmoothOpen W

/-- Lift the constructed output to the same entire resolved smooth locus. -/
def finiteResolvedSecantAddition :
    (finiteResolvedSecantOutputOpen hπ data j hj).toScheme ⟶ (U).toScheme :=
  finiteResolvedSecantOriginalSmooth hπ data j hj ≫ finiteOriginalToResolved hπ data j hj

/-- The resolved output contracts to exactly the new original secant formula. -/
@[reassoc] theorem finiteResolvedSecantAddition_contraction :
    finiteResolvedSecantAddition hπ data j hj ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      (finiteResolvedSecantOutputOpen hπ data j hj).ι ≫
        finiteResolvedSecantOriginalOutput hπ data j hj := by
  rw [finiteResolvedSecantAddition, Category.assoc, finiteOriginalToResolved_inclusion_assoc,
    finiteGlobalSmoothEmbedding_contraction, finiteResolvedSecantOriginalSmooth]
  exact morphismRestrict_ι _ _

/-- The lift retains the original coefficient point of the constructed secant output. -/
@[reassoc] theorem finiteResolvedSecantAddition_original_structure :
    finiteResolvedSecantAddition hπ data j hj ≫ (U).ι ≫ base =
      (finiteResolvedSecantOutputOpen hπ data j hj).ι ≫
        finiteResolvedSecantOriginalOutput hπ data j hj ≫ integralCurveStructure W := by
  exact finiteResolvedSecantAddition_contraction_assoc hπ data j hj (integralCurveStructure W)

/-- The local multiplication is over the same coefficient scheme as its two actual inputs. -/
@[reassoc] theorem finiteResolvedSecantAddition_structure :
    finiteResolvedSecantAddition hπ data j hj ≫ t =
      finiteResolvedSecantDomainMap hπ data j hj ≫ pullback.fst t t ≫ t := by
  rw [finiteResolvedSecantAddition_original_structure,
    finiteResolvedSecantOriginalOutput_structure]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTangentBranchLift
public import FLT.Mazur.WeierstrassDividedVerticalRefinement

/-!
# An explicit smooth neighborhood of the finite strict-branch output

Invert the constructed output derivative and lift to the full finite smooth
model. The complete original tangent contraction and coefficient point are
retained. Terminal residue coverage of this neighborhood is proved separately.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a2 b4' b6' : R)
  (h2 : W.a₂ = π ^ (start + j) * a2)
  (h4' : (data ⟨j, Nat.lt_succ_of_le hj⟩).b4 = π ^ (start + j) * b4')
  (h6' : (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 = π ^ (start + j) * b6')
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "s" => π ^ (start + j)
local notation "a" => dividedPairLeft W s (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W s (d).b3 (d).b4 (d).b6
local notation "B" => DividedTangentBranchRing W s (d).b3 (d).b4 (d).b6 a c
local notation "e" => dividedTangentBranchRestriction W s (d).b3 (d).b4 (d).b6 a c
local notation "v" => dividedTangentBranchLift W s (d).b3 (d).b4 (d).b6 a c
  a2 b4' b6' (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2
  (d).factor3 (d).factor4 (d).factor6 h4' h6'

local notation "out" => dividedTangentBranchOutput W s (d).b3 (d).b4 (d).b6 a c
  a2 b4' b6' (isRegular_iff_ne_zero.mpr (pow_ne_zero _ hπ)) h2
  (d).factor3 (d).factor4 (d).factor6 h4' h6'
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The explicit derivative cutting out smooth branch outputs. -/
def finiteTangentBranchDerivative : B := out (verticalDerivative W s (d).b3 (d).b4 (d).b6)

local notation "δ" => finiteTangentBranchDerivative hπ data j hj a2 b4' b6' h2 h4' h6'
local notation "i" => PrincipalAffineRefinement.inclusion δ
local notation "F" => finiteTangentBranchLift hπ data j hj a2 b4' b6' h2 h4' h6'

/-- The derivative neighborhood lies in the actual finite model's full smooth locus. -/
theorem finiteTangentBranchRefinement_range_smooth : Set.range (i ≫ F) ⊆ U := by
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq (finiteSecantDividedChart hπ data j hj) base
  simp only [finiteSecantDividedChart_structure] at h
  apply h.ge
  exact dividedVerticalRefinement_range_smooth W s (d).b3 (d).b4 (d).b6 out ⟨z, rfl⟩

/-- Construct the actual smooth output on its explicit principal neighborhood. -/
def finiteTangentBranchSmoothLift : Spec (.of (Localization.Away δ)) ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (i ≫ F) (by
    rw [Scheme.Opens.range_ι]
    exact finiteTangentBranchRefinement_range_smooth hπ data j hj a2 b4' b6' h2 h4' h6')

/-- The smooth output includes as the same branch output in the entire finite model. -/
@[reassoc] theorem finiteTangentBranchSmoothLift_inclusion :
    finiteTangentBranchSmoothLift hπ data j hj a2 b4' b6' h2 h4' h6' ≫ (U).ι = i ≫ F :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original tangent contraction is unchanged throughout this neighborhood. -/
@[reassoc] theorem finiteTangentBranchSmoothLift_contraction :
    finiteTangentBranchSmoothLift hπ data j hj a2 b4' b6' h2 h4' h6' ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      i ≫ Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
        dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 := by
  rw [finiteTangentBranchSmoothLift_inclusion_assoc,
    finiteTangentBranchLift_contraction]

/-- The smooth output retains the coefficient point of the actual branch source. -/
@[reassoc] theorem finiteTangentBranchSmoothLift_structure :
    finiteTangentBranchSmoothLift hπ data j hj a2 b4' b6' h2 h4' h6' ≫ (U).ι ≫ base =
      i ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteTangentBranchSmoothLift_inclusion_assoc,
    finiteTangentBranchLift_structure]

end FLT.Mazur.WeierstrassDividedDepth

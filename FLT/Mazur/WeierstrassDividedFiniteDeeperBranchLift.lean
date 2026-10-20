/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBranchLift
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput
public import FLT.Mazur.WeierstrassDividedVerticalRefinement

/-!
# Nonterminal branch outputs in the chosen entire finite model

When the final available depth is twice the input depth, insert the actual
deeper output into that model. Its derivative localization maps to the full
smooth locus, retaining the original tangent contraction and coefficient point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (d : Data W π k) (hl : start + j = k + k)
  (h2 : W.a₂ = 0)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "r" => dividedTangentBranchRestriction W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "v" => depthBranchLift hπ d e hl h2 a c
local notation "out" => depthBranchOutput hπ d e hl h2 a c
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Insert the genuine deeper output into the chosen entire finite model. -/
def finiteDeeperBranchLift : Spec (.of B) ⟶ finiteGlobalModel hπ data j hj :=
  v ≫ finiteSecantDividedChart hπ data j hj

local notation "F" => finiteDeeperBranchLift hπ data j hj d hl h2 a c

/-- The full deeper output retains the actual original tangent sum. -/
@[reassoc] theorem finiteDeeperBranchLift_contraction :
    F ≫ finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom (r).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [finiteDeeperBranchLift, Category.assoc, finiteSecantDividedChart_contraction]
  exact depthBranchLift_contraction ..

/-- The entire deeper output retains the source coefficient point. -/
@[reassoc] theorem finiteDeeperBranchLift_structure :
    F ≫ base = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteDeeperBranchLift, Category.assoc, finiteSecantDividedChart_structure]
  exact depthBranchLift_structure ..

/-- The pulled-back vertical derivative at the actual final depth. -/
def finiteDeeperBranchDerivative : B :=
  out (verticalDerivative W (π ^ (start + j)) (e).b3 (e).b4 (e).b6)

local notation "δ" => finiteDeeperBranchDerivative hπ data j hj d hl h2 a c
local notation "i" => PrincipalAffineRefinement.inclusion δ
variable [IsNoetherianRing R]

/-- The derivative neighborhood lands in the chosen finite model's full smooth locus. -/
theorem finiteDeeperBranchRefinement_range_smooth : Set.range (i ≫ F) ⊆ U := by
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq (finiteSecantDividedChart hπ data j hj) base
  simp only [finiteSecantDividedChart_structure] at h
  apply h.ge
  exact dividedVerticalRefinement_range_smooth W (π ^ (start + j))
    (e).b3 (e).b4 (e).b6 out ⟨z, rfl⟩

/-- The constructed deeper output on its explicit smooth principal neighborhood. -/
def finiteDeeperBranchSmoothLift : Spec (.of (Localization.Away δ)) ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (i ≫ F) (by
    rw [Scheme.Opens.range_ι]
    exact finiteDeeperBranchRefinement_range_smooth hπ data j hj d hl h2 a c)

/-- Including the smooth output recovers the entire finite-model output. -/
@[reassoc] theorem finiteDeeperBranchSmoothLift_inclusion :
    finiteDeeperBranchSmoothLift hπ data j hj d hl h2 a c ≫ (U).ι = i ≫ F :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth output retains exactly the original tangent contraction. -/
@[reassoc] theorem finiteDeeperBranchSmoothLift_contraction :
    finiteDeeperBranchSmoothLift hπ data j hj d hl h2 a c ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      i ≫ Spec.map (CommRingCat.ofHom (r).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [finiteDeeperBranchSmoothLift_inclusion_assoc, finiteDeeperBranchLift_contraction]

end FLT.Mazur.WeierstrassDividedDepth

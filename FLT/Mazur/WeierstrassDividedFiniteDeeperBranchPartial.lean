/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteDeeperBranchLift
public import FLT.Mazur.WeierstrassDividedHorizontalTerminal

/-!
# Both smooth neighborhoods of the finite deeper branch output

Use either actual partial derivative to construct a smooth output in the
same entire finite model. This includes the horizontal neighborhood needed
for terminal fibers where the vertical derivative can vanish.
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

local notation "F" => finiteDeeperBranchLift hπ data j hj d hl h2 a c
variable (r₀ : Fin 2)

/-- The selected partial derivative of the actual final-depth output. -/
def finiteDeeperBranchPartial : B :=
  out (dividedPartial W (π ^ (start + j)) (e).b3 (e).b4 (e).b6 r₀)

local notation "δ" => finiteDeeperBranchPartial hπ data j hj d hl h2 a c r₀
local notation "i" => PrincipalAffineRefinement.inclusion δ
variable [IsNoetherianRing R]

/-- The derivative neighborhood lands in the chosen finite model's full smooth locus. -/
theorem finiteDeeperBranchPartial_range_smooth : Set.range (i ≫ F) ⊆ U := by
  rintro _ ⟨z, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq (finiteSecantDividedChart hπ data j hj) base
  simp only [finiteSecantDividedChart_structure] at h
  apply h.ge
  exact dividedPartialRefinement_range_smooth W (π ^ (start + j))
    (e).b3 (e).b4 (e).b6 out r₀ ⟨z, rfl⟩

/-- The constructed deeper output on its explicit smooth principal neighborhood. -/
def finiteDeeperBranchPartialLift : Spec (.of (Localization.Away δ)) ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (i ≫ F) (by
    rw [Scheme.Opens.range_ι]
    exact finiteDeeperBranchPartial_range_smooth hπ data j hj d hl h2 a c r₀)

/-- Including the smooth output recovers the entire finite-model output. -/
@[reassoc] theorem finiteDeeperBranchPartialLift_inclusion :
    finiteDeeperBranchPartialLift hπ data j hj d hl h2 a c r₀ ≫ (U).ι = i ≫ F :=
  IsOpenImmersion.lift_fac _ _ _

/-- The smooth output retains exactly the original tangent contraction. -/
@[reassoc] theorem finiteDeeperBranchPartialLift_contraction :
    finiteDeeperBranchPartialLift hπ data j hj d hl h2 a c r₀ ≫ (U).ι ≫
        finiteGlobalContraction hπ data j hj =
      i ≫ Spec.map (CommRingCat.ofHom (r).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [finiteDeeperBranchPartialLift_inclusion_assoc, finiteDeeperBranchLift_contraction]

/-- The smooth neighborhood also retains the original source coefficient point. -/
@[reassoc] theorem finiteDeeperBranchPartialLift_structure :
    finiteDeeperBranchPartialLift hπ data j hj d hl h2 a c r₀ ≫ (U).ι ≫ base =
      i ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteDeeperBranchPartialLift_inclusion_assoc, finiteDeeperBranchLift_structure]

end FLT.Mazur.WeierstrassDividedDepth

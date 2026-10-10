/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueRetained
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleOverlap

/-!
# The retained transition between the actual residue principal opens

The next divided tensor fiber and the successive tensor fiber are compared on
their original principal opens. Their transition is the existing coordinate
substitution, conjugated by the proved coefficient comparisons.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (k + 1)) b3 b4 b6 K
local notation "e₀" => WeierstrassDilatation.residueRetainedTensorEquiv
  b3 b4 b6 D (k + 1) (Nat.zero_lt_succ k) hk h3 h4
local notation "e" => AlgEquiv.trans e₀ (WeierstrassDilatation.parameterEquiv W₀
  0 (0 * 0) 0 0 c 0 0 c (Eq.symm (zero_mul 0)) rfl rfl rfl)

/-- The actual principal open of the next divided tensor residue fiber. -/
abbrev ResidueDividedOpen := Localization.Away
  (WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K)

/-- The retained divided comparison transports the original principal open. -/
def residueDividedOpenEquiv :
    ResidueDividedOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K] DividedOpen W₀ 0 0 0 0 c :=
  PrincipalOpenTransport.equiv e _ _
    (by simp only [AlgEquiv.trans_apply,
      WeierstrassDilatation.residueRetainedTensorEquiv_x,
      WeierstrassDilatation.parameterEquiv_x])

/-- The comparison retains restriction of every original divided tensor function. -/
@[simp] theorem residueDividedOpenEquiv_base (z : T) :
    residueDividedOpenEquiv D k hk b3 b4 b6 h3 h4 (algebraMap T _ z) =
      algebraMap (WeierstrassDilatation.Coordinate W₀ (0 * 0) 0 0 c) _ (e z) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ _

/-- The actual divided and successive residue overlaps retain their original transition. -/
def residueMiddleTransition : ResidueDividedOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K]
    ResidueMiddleOpen (W := W) (π := π) k b3 b4 b6 :=
  (residueDividedOpenEquiv D k hk b3 b4 b6 h3 h4).trans
    ((overlapEquiv W₀ 0 0 0 0 c).trans
      (residueMiddleOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).symm)

/-- The transition square commutes with the original normalized overlap equivalence. -/
theorem residueMiddleTransition_square
    (z : ResidueDividedOpen (W := W) (π := π) k b3 b4 b6) :
    residueMiddleOpenEquiv D k hk0 hk b3 b4 b6 h3 h4
      (residueMiddleTransition D k hk0 hk b3 b4 b6 h3 h4 z) =
        overlapEquiv W₀ 0 0 0 0 c
          (residueDividedOpenEquiv D k hk b3 b4 b6 h3 h4 z) := by
  simp only [residueMiddleTransition, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]

/-- The actual next divided overlap is the same retained conic incidence open. -/
def residueDividedConicOpenEquiv :
    ResidueDividedOpen (W := W) (π := π) k b3 b4 b6 ≃ₐ[K] MiddleConicOpen W₀ c :=
  (residueDividedOpenEquiv D k hk b3 b4 b6 h3 h4).trans
    (middleDividedConicOverlap W₀ c ((residue_eq_zero_iff _).mpr D.a₂_mem))

/-- The two actual residue overlap charts agree on the original conic. -/
theorem residueMiddleTransition_conic
    (z : ResidueDividedOpen (W := W) (π := π) k b3 b4 b6) :
    residueMiddleConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4
      (residueMiddleTransition D k hk0 hk b3 b4 b6 h3 h4 z) =
        residueDividedConicOpenEquiv D k hk b3 b4 b6 h3 h4 z := by
  simp only [residueMiddleConicOpenEquiv, residueMiddleTransition,
    residueDividedConicOpenEquiv, middleDividedConicOverlap, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply]

end FLT.Mazur.WeierstrassSuccessiveX

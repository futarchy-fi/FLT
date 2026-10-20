/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedOriginalOpen
public import FLT.Mazur.OpenImmersionImageUnionGluing

/-!
# Two original-factor opens in the full resolved smooth product

Both factors of the ambient product range over the entire resolved smooth
locus. The two constructed open embeddings allow either factor to lie in
the original smooth group, while the other ranges over every component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

local notation "s" => integralSmoothStructure W
local notation "t" => (U).ι ≫ base
local notation "e" => finiteOriginalToResolved hπ data j hj

/-- The full relative product of two arbitrary resolved smooth inputs. -/
def finiteResolvedProduct : Scheme := pullback t t

/-- The open where the first factor is in the original smooth group. -/
def finiteResolvedLeftInput : pullback s t ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.map s t t t e (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, finiteOriginalToResolved_structure]) (by simp)

instance finiteResolvedLeftInput_open : IsOpenImmersion (finiteResolvedLeftInput hπ data j hj) := by
  unfold finiteResolvedLeftInput
  infer_instance

/-- The first projection is the actual original smooth embedding. -/
@[reassoc] theorem finiteResolvedLeftInput_fst :
    finiteResolvedLeftInput hπ data j hj ≫ pullback.fst t t = pullback.fst s t ≫ e := by
  simp only [finiteResolvedLeftInput, pullback.map, pullback.lift_fst]

/-- The second projection retains the entire resolved smooth input. -/
@[reassoc] theorem finiteResolvedLeftInput_snd :
    finiteResolvedLeftInput hπ data j hj ≫ pullback.snd t t = pullback.snd s t := by
  simp only [finiteResolvedLeftInput, pullback.map, pullback.lift_snd, Category.comp_id]

/-- Both orders of the original-factor open embed in the same full resolved product. -/
def finiteResolvedInput (b : Bool) : pullback s t ⟶ finiteResolvedProduct hπ data j hj :=
  if b then finiteResolvedLeftInput hπ data j hj ≫ (pullbackSymmetry t t).hom
  else finiteResolvedLeftInput hπ data j hj

instance finiteResolvedInput_open (b : Bool) :
    IsOpenImmersion (finiteResolvedInput hπ data j hj b) := by
  cases b <;> dsimp [finiteResolvedInput] <;> infer_instance

/-- On the right-hand domain the first input is fully resolved. -/
@[reassoc] theorem finiteResolvedRightInput_fst :
    finiteResolvedInput hπ data j hj true ≫ pullback.fst t t = pullback.snd s t := by
  simp only [finiteResolvedInput, ↓reduceIte, Category.assoc,
    pullbackSymmetry_hom_comp_fst, finiteResolvedLeftInput_snd]

/-- On the right-hand domain the second input is the original open embedding. -/
@[reassoc] theorem finiteResolvedRightInput_snd :
    finiteResolvedInput hπ data j hj true ≫ pullback.snd t t = pullback.fst s t ≫ e := by
  simp only [finiteResolvedInput, ↓reduceIte, Category.assoc,
    pullbackSymmetry_hom_comp_snd, finiteResolvedLeftInput_fst]

/-- The actual open union where at least one input is originally smooth. -/
def finiteResolvedOriginalFactorOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion (finiteResolvedInput hπ data j hj)

end FLT.Mazur.WeierstrassDividedDepth

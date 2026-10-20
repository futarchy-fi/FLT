/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteSmoothChart
public import FLT.Mazur.WeierstrassDividedResolvedProductOpens

/-!
# Both full divided smooth inputs in one later resolved product

Promote both actual smooth chart factors to the same supplied finite stage.
The product map is an open immersion and retains each original cubic input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (i : ℕ) (hi : i ≤ n)
  (j : ℕ) (hij : i ≤ j) (hj : j ≤ n)
local notation "d" => data ⟨i, Nat.lt_succ_of_le hi⟩
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ (start + i))
  (d).b3 (d).b4 (d).b6
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "V" => (s).smoothLocus
local notation "v" => (V).ι ≫ s
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "f" => finitePromotedDividedSmoothChart hπ data i hi j hij hj

/-- The full pair of actual divided smooth inputs in one common resolved product. -/
def finitePromotedDividedSmoothPair : pullback v v ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.map v v t t f f (𝟙 _) (by
    rw [Category.comp_id, finitePromotedDividedSmoothChart_structure]) (by
    rw [Category.comp_id, finitePromotedDividedSmoothChart_structure])

instance finitePromotedDividedSmoothPair_open :
    IsOpenImmersion (finitePromotedDividedSmoothPair hπ data i hi j hij hj) := by
  unfold finitePromotedDividedSmoothPair
  infer_instance

/-- The first entire smooth factor is promoted by the actual constructed stage map. -/
@[reassoc] theorem finitePromotedDividedSmoothPair_fst :
    finitePromotedDividedSmoothPair hπ data i hi j hij hj ≫ pullback.fst t t =
      pullback.fst v v ≫ f := by
  simp only [finitePromotedDividedSmoothPair, pullback.map, pullback.lift_fst]

/-- The second entire smooth factor is promoted to precisely the same finite stage. -/
@[reassoc] theorem finitePromotedDividedSmoothPair_snd :
    finitePromotedDividedSmoothPair hπ data i hi j hij hj ≫ pullback.snd t t =
      pullback.snd v v ≫ f := by
  simp only [finitePromotedDividedSmoothPair, pullback.map, pullback.lift_snd]

/-- The first full original divided input survives the common-stage embedding. -/
@[reassoc] theorem finitePromotedDividedSmoothPair_fst_contraction :
    finitePromotedDividedSmoothPair hπ data i hi j hij hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      pullback.fst v v ≫ (V).ι ≫ toCurve d := by
  rw [finitePromotedDividedSmoothPair_fst_assoc, finitePromotedDividedSmoothChart_contraction]

/-- The second full original divided input survives the common-stage embedding. -/
@[reassoc] theorem finitePromotedDividedSmoothPair_snd_contraction :
    finitePromotedDividedSmoothPair hπ data i hi j hij hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      pullback.snd v v ≫ (V).ι ≫ toCurve d := by
  rw [finitePromotedDividedSmoothPair_snd_assoc, finitePromotedDividedSmoothChart_contraction]

end FLT.Mazur.WeierstrassDividedDepth

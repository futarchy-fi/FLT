/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedUniversalSmoothPairIso
public import FLT.Mazur.WeierstrassDividedFiniteSmoothPairPromotion

/-!
# The universal supplied smooth pair embeds into the common resolved product

The entire tensor-pair smooth open is identified with the full smooth-chart
product and then embedded by the previously constructed finite-stage maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R]
  [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (i : ℕ) (hi : i ≤ n)
  (d : Data W π k) (hk : start + i = k) (j : ℕ) (hij : i ≤ j) (hj : j ≤ n)
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "a" => WeierstrassDilatation.dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => WeierstrassDilatation.dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "s" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "V" => (s).smoothLocus
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "a'" => Spec.map (CommRingCat.ofHom a.toRingHom)
local notation "c'" => Spec.map (CommRingCat.ofHom c.toRingHom)
local notation "emb" => finiteSuppliedDividedSmoothChart hπ data i hi d hk j hij hj

local notation "v" => (V).ι ≫ s
local notation "O" => suppliedDividedSmoothInputOpen d a c

/-- Promote both full supplied smooth-chart factors to the common finite model. -/
def finiteSuppliedSmoothProduct : pullback v v ⟶ finiteResolvedProduct hπ data j hj :=
  pullback.map v v t t emb emb (𝟙 _) (by
    rw [Category.comp_id, finiteSuppliedDividedSmoothChart_structure]) (by
    rw [Category.comp_id, finiteSuppliedDividedSmoothChart_structure])

instance finiteSuppliedSmoothProduct_open :
    IsOpenImmersion (finiteSuppliedSmoothProduct hπ data i hi d hk j hij hj) := by
  unfold finiteSuppliedSmoothProduct
  infer_instance

/-- For a family datum the promotion is exactly the existing full smooth-pair embedding. -/
theorem finiteSuppliedSmoothProduct_family :
    finiteSuppliedSmoothProduct hπ data i hi (data ⟨i, Nat.lt_succ_of_le hi⟩)
      rfl j hij hj = finitePromotedDividedSmoothPair hπ data i hi j hij hj := by
  rfl

/-- The supplied universal map is the full smooth-product identification followed by promotion. -/
theorem finiteSuppliedSmoothPair_universal :
    finiteSuppliedSmoothPair hπ data i hi d hk j hij hj a c =
      (universalDividedSmoothPairIso d).hom ≫
        finiteSuppliedSmoothProduct hπ data i hi d hk j hij hj := by
  apply pullback.hom_ext
  · simp only [finiteSuppliedSmoothPair_fst, Category.assoc, finiteSuppliedSmoothProduct,
      pullback.map, pullback.lift_fst, universalDividedSmoothPairIso_hom,
      universalDividedSmoothPair_fst_assoc]
    simp only [finiteSuppliedSmoothInput, universalDividedSmoothFactor, ↓reduceIte,
      Category.assoc]
  · simp only [finiteSuppliedSmoothPair_snd, Category.assoc, finiteSuppliedSmoothProduct,
      pullback.map, pullback.lift_snd, universalDividedSmoothPairIso_hom,
      universalDividedSmoothPair_snd_assoc]
    simp only [finiteSuppliedSmoothInput, universalDividedSmoothFactor, Bool.false_eq_true,
      ↓reduceIte, Category.assoc]

/-- The actual universal tensor-pair map is an open immersion in the resolved product. -/
instance finiteSuppliedSmoothPair_universal_open :
    IsOpenImmersion (finiteSuppliedSmoothPair hπ data i hi d hk j hij hj a c) := by
  rw [finiteSuppliedSmoothPair_universal]
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth

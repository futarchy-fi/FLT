/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTriplePromotedAddition
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothPair

/-!
# Exact-triple outputs and both smooth inputs in the same finite model

Intersect the constructed addition domain with the full smooth input locus.
The output and both inputs are actual maps to the same supplied finite stage,
retaining the original affine source and its coefficient structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure rootShearCurve
  nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
variable (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => tripleAdditionOpen D data hk a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

/-- The entire actual exact-triple output domain with both inputs relatively smooth. -/
def tripleSmoothSourceOpen : (Spec (.of S)).Opens := O ⊓ P

local notation "V" => tripleSmoothSourceOpen D data hk a c

/-- Both actual inputs in the same full resolved product that carries the previous partial law. -/
def tripleCommonInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  Scheme.homOfLE (Spec (.of S)) (show V ≤ P from inf_le_right) ≫
    finiteSuppliedSmoothPair hπ data k hk d rfl j hkj hj a c

/-- The constructed output promoted to the very same finite model as both inputs. -/
def tripleCommonOutput : (V).toScheme ⟶ (U).toScheme :=
  Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left) ≫
    triplePromotedAddition D data hk a c j hj hkj

/-- The common output retains the coefficient structure of the unchanged affine source. -/
@[reassoc] theorem tripleCommonOutput_structure :
    tripleCommonOutput D data hk a c j hj hkj ≫ t =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [tripleCommonOutput, Category.assoc, triplePromotedAddition_structure,
    Scheme.homOfLE_ι_assoc]

/-- The first common-model input retains the original supplied divided cubic point. -/
@[reassoc] theorem tripleCommonInput_fst_contraction :
    tripleCommonInput D data hk a c j hj hkj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d := by
  rw [tripleCommonInput, Category.assoc, finiteSuppliedSmoothPair_fst_assoc,
    finiteSuppliedSmoothInput_contraction]
  exact Scheme.homOfLE_ι_assoc _ _ _

/-- The second common-model input retains the original supplied divided cubic point. -/
@[reassoc] theorem tripleCommonInput_snd_contraction :
    tripleCommonInput D data hk a c j hj hkj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫ toCurve d := by
  rw [tripleCommonInput, Category.assoc, finiteSuppliedSmoothPair_snd_assoc,
    finiteSuppliedSmoothInput_contraction]
  exact Scheme.homOfLE_ι_assoc _ _ _

/-- The common pair and the common output lie over precisely the same coefficient point. -/
@[reassoc] theorem tripleCommonInput_structure :
    tripleCommonInput D data hk a c j hj hkj ≫ pullback.fst t t ≫ t =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [tripleCommonInput, Category.assoc, finiteSuppliedSmoothPair_fst_assoc,
    finiteSuppliedSmoothInput_structure, Scheme.homOfLE_ι_assoc]

end FLT.Mazur.WeierstrassDividedDepth

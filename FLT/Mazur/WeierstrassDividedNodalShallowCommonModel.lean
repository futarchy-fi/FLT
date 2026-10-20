/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowPromotedAddition
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothPair

/-!
# Shallow outputs and both smooth inputs in the same finite model

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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j) (hrj : m - 2 * k ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalShallowAdditionOpen D hdepth hm data hr d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

/-- The entire actual shallow output domain with both inputs relatively smooth. -/
def nodalShallowSmoothSourceOpen : (Spec (.of S)).Opens := O ⊓ P

local notation "V" => nodalShallowSmoothSourceOpen D hdepth hm data hr d a c

/-- Both actual inputs in the same full resolved product that carries the previous partial law. -/
def nodalShallowCommonInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  Scheme.homOfLE (Spec (.of S)) (show V ≤ P from inf_le_right) ≫
    finiteSuppliedSmoothPair hπ data k (hkj.trans hj) d (Nat.zero_add k) j hkj hj a c

/-- The constructed output promoted to the very same finite model as both inputs. -/
def nodalShallowCommonOutput : (V).toScheme ⟶ (U).toScheme :=
  Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left) ≫
    nodalShallowPromotedAddition D hdepth hm data hr d a c j hj hrj

/-- The common output retains the coefficient structure of the unchanged affine source. -/
@[reassoc] theorem nodalShallowCommonOutput_structure :
    nodalShallowCommonOutput D hdepth hm data hr d a c j hj hrj ≫ t =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalShallowCommonOutput, Category.assoc, nodalShallowPromotedAddition_structure,
    Scheme.homOfLE_ι_assoc]

/-- The first common-model input retains the original supplied divided cubic point. -/
@[reassoc] theorem nodalShallowCommonInput_fst_contraction :
    nodalShallowCommonInput D hdepth hm data hr d a c j hj hkj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d := by
  rw [nodalShallowCommonInput, Category.assoc, finiteSuppliedSmoothPair_fst_assoc,
    finiteSuppliedSmoothInput_contraction]
  exact Scheme.homOfLE_ι_assoc _ _ _

/-- The second common-model input retains the original supplied divided cubic point. -/
@[reassoc] theorem nodalShallowCommonInput_snd_contraction :
    nodalShallowCommonInput D hdepth hm data hr d a c j hj hkj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫ toCurve d := by
  rw [nodalShallowCommonInput, Category.assoc, finiteSuppliedSmoothPair_snd_assoc,
    finiteSuppliedSmoothInput_contraction]
  exact Scheme.homOfLE_ι_assoc _ _ _

/-- The common pair and the common output lie over precisely the same coefficient point. -/
@[reassoc] theorem nodalShallowCommonInput_structure :
    nodalShallowCommonInput D hdepth hm data hr d a c j hj hkj ≫ pullback.fst t t ≫ t =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalShallowCommonInput, Category.assoc, finiteSuppliedSmoothPair_fst_assoc,
    finiteSuppliedSmoothInput_structure, Scheme.homOfLE_ι_assoc]

end FLT.Mazur.WeierstrassDividedDepth

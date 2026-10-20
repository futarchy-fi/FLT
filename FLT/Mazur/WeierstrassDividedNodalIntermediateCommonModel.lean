/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediatePromotedAddition
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothPair

/-!
# Intermediate outputs and both smooth inputs in the same finite model

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
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j) (hrj : k + r ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hr d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

/-- The entire actual intermediate output domain with both inputs relatively smooth. -/
def nodalIntermediateSmoothSourceOpen : (Spec (.of S)).Opens := O ⊓ P

local notation "V" => nodalIntermediateSmoothSourceOpen D hdepth hrk hrm data hr d a c

/-- Both actual inputs in the same full resolved product that carries the previous partial law. -/
def nodalIntermediateCommonInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  Scheme.homOfLE (Spec (.of S)) (show V ≤ P from inf_le_right) ≫
    finiteSuppliedSmoothPair hπ data k (hkj.trans hj) d (Nat.zero_add k) j hkj hj a c

/-- The constructed output promoted to the very same finite model as both inputs. -/
def nodalIntermediateCommonOutput : (V).toScheme ⟶ (U).toScheme :=
  Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left) ≫
    nodalIntermediatePromotedAddition D hdepth hrk hrm data hr d a c j hj hrj

/-- The common output retains the coefficient structure of the unchanged affine source. -/
@[reassoc] theorem nodalIntermediateCommonOutput_structure :
    nodalIntermediateCommonOutput D hdepth hrk hrm data hr d a c j hj hrj ≫ t =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalIntermediateCommonOutput, Category.assoc, nodalIntermediatePromotedAddition_structure,
    Scheme.homOfLE_ι_assoc]

/-- The first common-model input retains the original supplied divided cubic point. -/
@[reassoc] theorem nodalIntermediateCommonInput_fst_contraction :
    nodalIntermediateCommonInput D hdepth hrk hrm data hr d a c j hj hkj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d := by
  rw [nodalIntermediateCommonInput, Category.assoc, finiteSuppliedSmoothPair_fst_assoc,
    finiteSuppliedSmoothInput_contraction]
  exact Scheme.homOfLE_ι_assoc _ _ _

/-- The second common-model input retains the original supplied divided cubic point. -/
@[reassoc] theorem nodalIntermediateCommonInput_snd_contraction :
    nodalIntermediateCommonInput D hdepth hrk hrm data hr d a c j hj hkj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫ toCurve d := by
  rw [nodalIntermediateCommonInput, Category.assoc, finiteSuppliedSmoothPair_snd_assoc,
    finiteSuppliedSmoothInput_contraction]
  exact Scheme.homOfLE_ι_assoc _ _ _

/-- The common pair and the common output lie over precisely the same coefficient point. -/
@[reassoc] theorem nodalIntermediateCommonInput_structure :
    nodalIntermediateCommonInput D hdepth hrk hrm data hr d a c j hj hkj ≫ pullback.fst t t ≫ t =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalIntermediateCommonInput, Category.assoc, finiteSuppliedSmoothPair_fst_assoc,
    finiteSuppliedSmoothInput_structure, Scheme.homOfLE_ι_assoc]

end FLT.Mazur.WeierstrassDividedDepth

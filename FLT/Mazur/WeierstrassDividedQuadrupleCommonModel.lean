/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalQuadrupleAdditionSourceCoverage
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothPair

/-!
# Quadruple-depth outputs and both smooth inputs in the same finite model

Intersect the constructed addition domain with the full smooth input locus.
The output and both inputs are actual maps to the same constructed doubled stage,
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
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (4 * k)) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "data" => splitNodeDoubledFamily D
local notation "j" => k + k
local notation "hj" => (le_rfl : k + k ≤ k + k)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

/-- The entire actual quadruple-depth output domain with both inputs relatively smooth. -/
def quadrupleSmoothSourceOpen : (Spec (.of S)).Opens := O ⊓ P

local notation "V" => quadrupleSmoothSourceOpen D d a c

/-- Both actual inputs in the same full resolved product that carries the previous partial law. -/
def quadrupleCommonInput : (V).toScheme ⟶ finiteResolvedProduct hπ data j hj :=
  Scheme.homOfLE (Spec (.of S)) (show V ≤ P from inf_le_right) ≫
    finiteSuppliedSmoothPair hπ data k (by omega) d (Nat.zero_add k) j (by omega) hj a c

/-- The constructed output in the very same finite model as both inputs. -/
def quadrupleCommonOutput : (V).toScheme ⟶ (U).toScheme :=
  Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left) ≫
    nodalQuadrupleAddition D d a c

/-- The common output retains the coefficient structure of the unchanged affine source. -/
@[reassoc] theorem quadrupleCommonOutput_structure :
    quadrupleCommonOutput D d a c ≫ t =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [quadrupleCommonOutput, Category.assoc, nodalQuadrupleAddition_structure,
    Scheme.homOfLE_ι_assoc]

/-- The first common-model input retains the original supplied divided cubic point. -/
@[reassoc] theorem quadrupleCommonInput_fst_contraction :
    quadrupleCommonInput D d a c ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d := by
  rw [quadrupleCommonInput, Category.assoc, finiteSuppliedSmoothPair_fst_assoc,
    finiteSuppliedSmoothInput_contraction]
  exact Scheme.homOfLE_ι_assoc _ _ _

/-- The second common-model input retains the original supplied divided cubic point. -/
@[reassoc] theorem quadrupleCommonInput_snd_contraction :
    quadrupleCommonInput D d a c ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (V).ι ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫ toCurve d := by
  rw [quadrupleCommonInput, Category.assoc, finiteSuppliedSmoothPair_snd_assoc,
    finiteSuppliedSmoothInput_contraction]
  exact Scheme.homOfLE_ι_assoc _ _ _

/-- The common pair and the common output lie over precisely the same coefficient point. -/
@[reassoc] theorem quadrupleCommonInput_structure :
    quadrupleCommonInput D d a c ≫ pullback.fst t t ≫ t =
      (V).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [quadrupleCommonInput, Category.assoc, finiteSuppliedSmoothPair_fst_assoc,
    finiteSuppliedSmoothInput_structure, Scheme.homOfLE_ι_assoc]

end FLT.Mazur.WeierstrassDividedDepth

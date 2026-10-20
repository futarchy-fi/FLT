/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleCommonFormula
public import FLT.Mazur.WeierstrassDividedCrossDepthRightTangent
public import FLT.Mazur.WeierstrassDividedCrossDepthRightSecant

/-!
# The entire quadruple-depth overlap with the originally smooth right action

Cross-depth comparisons identify both local formulas, and the pulled-back
quadruple-depth cover extends the equality to the full common source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
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

local notation "V" => quadrupleSmoothSourceOpen D d a c
local notation "src" => nodalQuadrupleAdditionSource D d a c
local notation "inc" => nodalQuadrupleAdditionInclusion D d a c
local notation "out" => nodalQuadrupleAdditionOutput D d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)

local notation "Ot" => nodalTangentBranchOutputOpen D d a c
local notation "T" => DividedTangentRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "pair" => quadrupleCommonInput D d a c

local notation "Os" => ⨆ i, nodalQuadrupleSecantLocalOpen D d a c i
local notation "E" => DividedSecantRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c
local notation "es" => IsScalarTower.toAlgHom R S E

/-- The right action agrees with the constructed quadruple-depth output on a tangent refinement. -/
theorem quadrupleCommonOutput_rightLocalTangent {X : Scheme}
    (p : X ⟶ pullback (integralSmoothStructure W) t) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ finiteResolvedInput hπ data j hj true = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc true) :
    p ≫ finiteGlobalSmoothAction hπ data j hj =
      q ≫ quadrupleCommonOutput D d a c := by
  have ha : p ≫ finiteResolvedInput hπ data j hj true ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ finiteResolvedInput hπ data j hj true ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply finiteResolvedRight_crossDepthTangentOverlap hπ data j hj d a c
    p (r ≫ (Ot).ι) ha hc
  rw [← Category.assoc,
    quadrupleCommonOutput_local D d a c true q r hqr]
  simp only [Category.assoc, nodalQuadrupleAdditionOutput, nodalTangentGluedOutput_contraction]

/-- The right action agrees with the constructed quadruple-depth output on a secant refinement. -/
theorem quadrupleCommonOutput_rightLocalSecant {X : Scheme}
    (p : X ⟶ pullback (integralSmoothStructure W) t) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Os).toScheme) [Flat r]
    (hpq : p ≫ finiteResolvedInput hπ data j hj true = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc false) :
    p ≫ finiteGlobalSmoothAction hπ data j hj =
      q ≫ quadrupleCommonOutput D d a c := by
  have ha : p ≫ finiteResolvedInput hπ data j hj true ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ finiteResolvedInput hπ data j hj true ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply finiteResolvedRight_crossDepthSecantOverlap hπ data j hj d a c
    p (r ≫ (Os).ι) ha hc
  rw [← Category.assoc,
    quadrupleCommonOutput_local D d a c false q r hqr]
  simp only [Category.assoc,
    nodalQuadrupleAdditionOutput,
    nodalQuadrupleSecantGluedOutput_contraction]

/-- Every flat refinement of the entire quadruple-depth/right-action overlap has equal outputs. -/
theorem quadrupleCommonOutput_rightOverlap {X : Scheme}
    (p : X ⟶ pullback (integralSmoothStructure W) t) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ finiteResolvedInput hπ data j hj true = q ≫ pair) :
    p ≫ finiteGlobalSmoothAction hπ data j hj =
      q ≫ quadrupleCommonOutput D d a c := by
  let v := Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left)
  apply Scheme.Cover.hom_ext ((C).pullback₁ (q ≫ v))
  intro b
  let f := pullback.fst (q ≫ v) ((C).f b)
  let g := pullback.snd (q ≫ v) ((C).f b)
  let r := g ≫ (inc b).isoOpensRange.inv
  have hq : f ≫ q ≫ v = g ≫ (C).f b := pullback.condition
  have hi : (C).f b ≫ (O).ι = (inc b).opensRange.ι :=
    Scheme.homOfLE_ι _ (le_iSup (fun i => (inc i).opensRange) b)
  have he : (f ≫ q) ≫ (V).ι = r ≫ inc b := by
    have h := congrArg (· ≫ (O).ι) hq
    simpa only [r, v, Category.assoc, hi, Scheme.homOfLE_ι,
      Scheme.Hom.isoOpensRange_inv_comp] using h
  have hp : (f ≫ p) ≫ finiteResolvedInput hπ data j hj true =
      (f ≫ q) ≫ pair := by rw [Category.assoc, hpq, Category.assoc]
  cases b with
  | false =>
    exact quadrupleCommonOutput_rightLocalSecant D d a c (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact quadrupleCommonOutput_rightLocalTangent D d a c (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth

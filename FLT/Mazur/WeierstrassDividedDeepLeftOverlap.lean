/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepCommonFormula
public import FLT.Mazur.WeierstrassDividedCrossDepthLeftTangent
public import FLT.Mazur.WeierstrassDividedCrossDepthLeftSecant

/-!
# The entire deep-node overlap with the originally smooth left action

Cross-depth comparisons identify both local formulas, and the pulled-back
deep-node cover extends the equality to the full common source.
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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ}
  (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hkk : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
variable (j : ℕ) (hj : j ≤ n) (hkj : k + k ≤ j)
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalDeepAdditionOpen D data hkk d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => deepSmoothSourceOpen D data hkk d a c
local notation "src" => nodalDeepAdditionSource D data hkk d a c
local notation "inc" => nodalDeepAdditionInclusion D data hkk d a c
local notation "out" => nodalDeepAdditionOutput D data hkk d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data (k + k) j hkj hj

local notation "Ot" => deepNodalTangentBranchOutputOpen D data hkk d a c
local notation "T" => DividedTangentRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "pair" => deepCommonInput D data hkk d a c j hj hkj

local notation "Os" => ⨆ i, nodalDeepSecantLocalOpen D data hkk d a c i
local notation "E" => DividedSecantRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c
local notation "es" => IsScalarTower.toAlgHom R S E

/-- The left action agrees with the constructed deep-node output on a tangent refinement. -/
theorem deepCommonOutput_leftLocalTangent {X : Scheme}
    (p : X ⟶ pullback (integralSmoothStructure W) t) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ finiteResolvedLeftInput hπ data j hj = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc true) :
    p ≫ finiteGlobalSmoothAction hπ data j hj =
      q ≫ deepCommonOutput D data hkk d a c j hj hkj := by
  have ha : p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      deepCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalDeepAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      deepCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalDeepAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply finiteResolvedLeft_crossDepthTangentOverlap hπ data j hj d a c
    p (r ≫ (Ot).ι) ha hc
  rw [← Category.assoc,
    deepCommonOutput_local D data hkk d a c j hj hkj true q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    nodalDeepAdditionOutput, deepNodalTangentGluedOutput_contraction]

/-- The left action agrees with the constructed deep-node output on a secant refinement. -/
theorem deepCommonOutput_leftLocalSecant {X : Scheme}
    (p : X ⟶ pullback (integralSmoothStructure W) t) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Os).toScheme) [Flat r]
    (hpq : p ≫ finiteResolvedLeftInput hπ data j hj = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc false) :
    p ≫ finiteGlobalSmoothAction hπ data j hj =
      q ≫ deepCommonOutput D data hkk d a c j hj hkj := by
  have ha : p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      deepCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalDeepAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ finiteResolvedLeftInput hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      deepCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalDeepAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply finiteResolvedLeft_crossDepthSecantOverlap hπ data j hj d a c
    p (r ≫ (Os).ι) ha hc
  rw [← Category.assoc,
    deepCommonOutput_local D data hkk d a c j hj hkj false q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    nodalDeepAdditionOutput, nodalDeepSecantGluedOutput_contraction]

/-- Every flat refinement of the entire deep-node/left-action overlap has equal outputs. -/
theorem deepCommonOutput_leftOverlap {X : Scheme}
    (p : X ⟶ pullback (integralSmoothStructure W) t) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ finiteResolvedLeftInput hπ data j hj = q ≫ pair) :
    p ≫ finiteGlobalSmoothAction hπ data j hj =
      q ≫ deepCommonOutput D data hkk d a c j hj hkj := by
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
  have hp : (f ≫ p) ≫ finiteResolvedLeftInput hπ data j hj =
      (f ≫ q) ≫ pair := by rw [Category.assoc, hpq, Category.assoc]
  cases b with
  | false =>
    exact deepCommonOutput_leftLocalSecant D data hkk d a c
      j hj hkj (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact deepCommonOutput_leftLocalTangent D data hkk d a c
      j hj hkj (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth

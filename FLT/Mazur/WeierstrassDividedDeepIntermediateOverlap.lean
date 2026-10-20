/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepCommonFormula
public import FLT.Mazur.WeierstrassDividedNodalIntermediateCrossDepthTangent
public import FLT.Mazur.WeierstrassDividedNodalIntermediateCrossDepthSecant

/-!
# The full cross-depth intermediate/deep-node overlap

Cross-depth comparisons identify both local formulas, and the pulled-back
deep-node cover extends the equality to the full common source. Both input
depths and supplied coefficient algebras are independent.
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
variable {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S'] [Module.Flat R S'] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hkk : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (j : ℕ) (hj : j ≤ n) (hkj : k + k ≤ j)
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
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
variable {l r : ℕ} (hs : 3 * l ≤ m) (hrl : r ≤ l) (hrm : r ≤ m - 3 * l)
  (hsn : l + r ≤ n) (d' : Data W π l)
  (a' c' : Coordinate W (π ^ l) d'.b3 d'.b4 d'.b6 →ₐ[R] S')
  (hlj : l ≤ j) (hsj : l + r ≤ j)
local notation "Rcp" => nodalIntermediateSmoothSourceOpen D hs hrl hrm data hsn d' a' c'
local notation "intermediatePair" =>
  nodalIntermediateCommonInput D hs hrl hrm data hsn d' a' c' j hj hlj
local notation "intermediateOut" =>
  nodalIntermediateCommonOutput D hs hrl hrm data hsn d' a' c' j hj hsj
local notation "pair" => deepCommonInput D data hkk d a c j hj hkj

local notation "Os" => ⨆ i, nodalDeepSecantLocalOpen D data hkk d a c i
local notation "E" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "es" => IsScalarTower.toAlgHom R S E

/-- The intermediate law agrees with the constructed deep-node output on a tangent refinement. -/
theorem deepCommonOutput_intermediateLocalTangent {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ intermediatePair = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc true) :
    p ≫ intermediateOut =
      q ≫ deepCommonOutput D data hkk d a c j hj hkj := by
  have ha : p ≫ intermediatePair ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      deepCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalDeepAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ intermediatePair ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      deepCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalDeepAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply nodalIntermediateCommonOutput_crossDepthTangentOverlap D hs hrl hrm data hsn d' a' c'
    j hj hsj d a c p (r ≫ (Ot).ι)
    (by simpa only [nodalIntermediateCommonInput_fst_contraction] using ha)
    (by simpa only [nodalIntermediateCommonInput_snd_contraction] using hc)
  rw [← Category.assoc,
    deepCommonOutput_local D data hkk d a c j hj hkj true q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    nodalDeepAdditionOutput, deepNodalTangentGluedOutput_contraction]

/-- The intermediate law agrees with the constructed deep-node output on a secant refinement. -/
theorem deepCommonOutput_intermediateLocalSecant {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Os).toScheme) [Flat r]
    (hpq : p ≫ intermediatePair = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc false) :
    p ≫ intermediateOut =
      q ≫ deepCommonOutput D data hkk d a c j hj hkj := by
  have ha : p ≫ intermediatePair ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      deepCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalDeepAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ intermediatePair ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      deepCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalDeepAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply nodalIntermediateCommonOutput_crossDepthSecantOverlap D hs hrl hrm data hsn d' a' c'
    j hj hsj d a c p (r ≫ (Os).ι)
    (by simpa only [nodalIntermediateCommonInput_fst_contraction] using ha)
    (by simpa only [nodalIntermediateCommonInput_snd_contraction] using hc)
  rw [← Category.assoc,
    deepCommonOutput_local D data hkk d a c j hj hkj false q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    nodalDeepAdditionOutput, nodalDeepSecantGluedOutput_contraction]

/-- Every flat refinement of the entire deep-node/intermediate overlap has equal outputs. -/
theorem deepCommonOutput_intermediateOverlap {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ intermediatePair = q ≫ pair) :
    p ≫ intermediateOut =
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
  have hp : (f ≫ p) ≫ intermediatePair =
      (f ≫ q) ≫ pair := by rw [Category.assoc, hpq, Category.assoc]
  cases b with
  | false =>
    exact deepCommonOutput_intermediateLocalSecant D data hkk d a c
      j hj hkj hs hrl hrm hsn d' a' c' hlj hsj (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact deepCommonOutput_intermediateLocalTangent D data hkk d a c
      j hj hkj hs hrl hrm hsn d' a' c' hlj hsj (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth

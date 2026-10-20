/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleCommonFormula
public import FLT.Mazur.WeierstrassDividedNodalShallowCrossDepthTangent
public import FLT.Mazur.WeierstrassDividedNodalShallowCrossDepthSecant

/-!
# The full cross-depth shallow/quadruple-depth overlap

Cross-depth comparisons identify both local formulas, and the pulled-back
quadruple-depth cover extends the equality to the full common source. Both input
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
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
variable {l m : ℕ} (D' : SplitNodeDepth W π m) (hs : 2 * l ≤ m) (hsm : m ≤ 3 * l)
  (hsn : m - 2 * l ≤ k + k) (d' : Data W π l)
  (a' c' : Coordinate W (π ^ l) d'.b3 d'.b4 d'.b6 →ₐ[R] S')
  (hlj : l ≤ k + k) (hsj : m - 2 * l ≤ k + k)
local notation "Rcp" => nodalShallowSmoothSourceOpen D' hs hsm data hsn d' a' c'
local notation "shallowPair" => nodalShallowCommonInput D' hs hsm data hsn d' a' c' j hj hlj
local notation "shallowOut" => nodalShallowCommonOutput D' hs hsm data hsn d' a' c' j hj hsj
local notation "pair" => quadrupleCommonInput D d a c

local notation "Os" => ⨆ i, nodalQuadrupleSecantLocalOpen D d a c i
local notation "E" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "es" => IsScalarTower.toAlgHom R S E

/-- The shallow law agrees with the constructed quadruple-depth output on a tangent refinement. -/
theorem quadrupleCommonOutput_shallowLocalTangent {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ shallowPair = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc true) :
    p ≫ shallowOut =
      q ≫ quadrupleCommonOutput D d a c := by
  have ha : p ≫ shallowPair ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ shallowPair ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply nodalShallowCommonOutput_crossDepthTangentOverlap D' hs hsm data hsn d' a' c'
    j hj hsj d a c p (r ≫ (Ot).ι)
    (by simpa only [nodalShallowCommonInput_fst_contraction] using ha)
    (by simpa only [nodalShallowCommonInput_snd_contraction] using hc)
  rw [← Category.assoc,
    quadrupleCommonOutput_local D d a c true q r hqr]
  simp only [Category.assoc,
    nodalQuadrupleAdditionOutput, nodalTangentGluedOutput_contraction]

/-- The shallow law agrees with the constructed quadruple-depth output on a secant refinement. -/
theorem quadrupleCommonOutput_shallowLocalSecant {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Os).toScheme) [Flat r]
    (hpq : p ≫ shallowPair = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc false) :
    p ≫ shallowOut =
      q ≫ quadrupleCommonOutput D d a c := by
  have ha : p ≫ shallowPair ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ shallowPair ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply nodalShallowCommonOutput_crossDepthSecantOverlap D' hs hsm data hsn d' a' c'
    j hj hsj d a c p (r ≫ (Os).ι)
    (by simpa only [nodalShallowCommonInput_fst_contraction] using ha)
    (by simpa only [nodalShallowCommonInput_snd_contraction] using hc)
  rw [← Category.assoc,
    quadrupleCommonOutput_local D d a c false q r hqr]
  simp only [Category.assoc,
    nodalQuadrupleAdditionOutput, nodalQuadrupleSecantGluedOutput_contraction]

/-- Every flat refinement of the entire quadruple-depth/shallow overlap has equal outputs. -/
theorem quadrupleCommonOutput_shallowOverlap {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ shallowPair = q ≫ pair) :
    p ≫ shallowOut =
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
  have hp : (f ≫ p) ≫ shallowPair =
      (f ≫ q) ≫ pair := by rw [Category.assoc, hpq, Category.assoc]
  cases b with
  | false =>
    exact quadrupleCommonOutput_shallowLocalSecant D d a c
      D' hs hsm hsn d' a' c' hlj hsj (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact quadrupleCommonOutput_shallowLocalTangent D d a c
      D' hs hsm hsn d' a' c' hlj hsj (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth

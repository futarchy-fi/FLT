/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleCommonFormula
public import FLT.Mazur.WeierstrassDividedTripleCrossDepthTangent
public import FLT.Mazur.WeierstrassDividedTripleCrossDepthSecant

/-!
# The full cross-depth triple/quadruple-depth overlap

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
variable {l : ℕ} (D' : SplitNodeDepth W π (3 * (0 + l))) (hl : l ≤ k + k)
local notation "d'" => data ⟨l, Nat.lt_succ_of_le hl⟩
variable (a' c' : Coordinate W (π ^ (0 + l))
  (splitNodeDoubledFamily D ⟨l, Nat.lt_succ_of_le hl⟩).b3
  (splitNodeDoubledFamily D ⟨l, Nat.lt_succ_of_le hl⟩).b4
  (splitNodeDoubledFamily D ⟨l, Nat.lt_succ_of_le hl⟩).b6 →ₐ[R] S')
  (hlj : l ≤ k + k)
local notation "Rcp" => tripleSmoothSourceOpen D' data hl a' c'
local notation "triplePair" => tripleCommonInput D' data hl a' c' j hj hlj
local notation "tripleOut" => tripleCommonOutput D' data hl a' c' j hj hlj
local notation "pair" => quadrupleCommonInput D d a c

local notation "Os" => ⨆ i, nodalQuadrupleSecantLocalOpen D d a c i
local notation "E" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "es" => IsScalarTower.toAlgHom R S E

/-- The triple law agrees with the constructed quadruple-depth output on a tangent refinement. -/
theorem quadrupleCommonOutput_tripleLocalTangent {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ triplePair = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc true) :
    p ≫ tripleOut =
      q ≫ quadrupleCommonOutput D d a c := by
  have ha : p ≫ triplePair ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ triplePair ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply tripleCommonOutput_crossDepthTangentOverlap D' data hl a' c'
    j hj hlj d a c p (r ≫ (Ot).ι)
    (by simpa only [tripleCommonInput_fst_contraction] using ha)
    (by simpa only [tripleCommonInput_snd_contraction] using hc)
  rw [← Category.assoc,
    quadrupleCommonOutput_local D d a c true q r hqr]
  simp only [Category.assoc,
    nodalQuadrupleAdditionOutput, nodalTangentGluedOutput_contraction]

/-- The triple law agrees with the constructed quadruple-depth output on a secant refinement. -/
theorem quadrupleCommonOutput_tripleLocalSecant {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Os).toScheme) [Flat r]
    (hpq : p ≫ triplePair = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc false) :
    p ≫ tripleOut =
      q ≫ quadrupleCommonOutput D d a c := by
  have ha : p ≫ triplePair ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ triplePair ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      quadrupleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply tripleCommonOutput_crossDepthSecantOverlap D' data hl a' c'
    j hj hlj d a c p (r ≫ (Os).ι)
    (by simpa only [tripleCommonInput_fst_contraction] using ha)
    (by simpa only [tripleCommonInput_snd_contraction] using hc)
  rw [← Category.assoc,
    quadrupleCommonOutput_local D d a c false q r hqr]
  simp only [Category.assoc,
    nodalQuadrupleAdditionOutput, nodalQuadrupleSecantGluedOutput_contraction]

/-- Every flat refinement of the entire quadruple-depth/triple overlap has equal outputs. -/
theorem quadrupleCommonOutput_tripleOverlap {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ triplePair = q ≫ pair) :
    p ≫ tripleOut =
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
  have hp : (f ≫ p) ≫ triplePair =
      (f ≫ q) ≫ pair := by rw [Category.assoc, hpq, Category.assoc]
  cases b with
  | false =>
    exact quadrupleCommonOutput_tripleLocalSecant D d a c
      D' hl a' c' hlj (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact quadrupleCommonOutput_tripleLocalTangent D d a c
      D' hl a' c' hlj (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth

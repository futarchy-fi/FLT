/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleCommonFormula
public import FLT.Mazur.WeierstrassDividedNodalShallowCrossDepthTangent
public import FLT.Mazur.WeierstrassDividedNodalShallowCrossDepthSecant

/-!
# Compare the entire exact-triple and shallow laws

Both actual formula charts compare through the original input contractions.
Pulling back the exact-triple cover proves equality on the whole overlap.
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
  {W : WeierstrassCurve R} {π : R} {n k : ℕ}
  (D : SplitNodeDepth W π (3 * (0 + k)))
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (0 + k))
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

local notation "V" => tripleSmoothSourceOpen D data hk a c
local notation "src" => tripleAdditionSource D data hk a c
local notation "inc" => tripleAdditionInclusion D data hk a c
local notation "out" => tripleAdditionOutput D data hk a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data k j hkj hj

local notation "Ot" => tripleTangentBranchOutputOpen D data hk a c
local notation "T" => DividedTangentRing W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
variable {l : ℕ} (hs : 2 * l ≤ 3 * (0 + k)) (hsm : 3 * (0 + k) ≤ 3 * l)
  (hsn : 3 * (0 + k) - 2 * l ≤ n) (d' : Data W π l)
  (a' c' : Coordinate W (π ^ l) d'.b3 d'.b4 d'.b6 →ₐ[R] S')
  (hlj : l ≤ j) (hsj : 3 * (0 + k) - 2 * l ≤ j)
local notation "Rcp" => nodalShallowSmoothSourceOpen D hs hsm data hsn d' a' c'
local notation "shallowPair" => nodalShallowCommonInput D hs hsm data hsn d' a' c' j hj hlj
local notation "shallowOut" => nodalShallowCommonOutput D hs hsm data hsn d' a' c' j hj hsj
local notation "pair" => tripleCommonInput D data hk a c j hj hkj

local notation "Os" => ⨆ i, tripleSecantLocalOpen D data hk a c i
local notation "E" => DividedSecantRing W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6 a c
local notation "es" => IsScalarTower.toAlgHom R S E

/-- The shallow law agrees with the constructed exact-triple output on a tangent refinement. -/
theorem tripleCommonOutput_shallowLocalTangent {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ shallowPair = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc true) :
    p ≫ shallowOut =
      q ≫ tripleCommonOutput D data hk a c j hj hkj := by
  have ha : p ≫ shallowPair ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      tripleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [tripleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ shallowPair ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      tripleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [tripleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply nodalShallowCommonOutput_crossDepthTangentOverlap D hs hsm data hsn d' a' c'
    j hj hsj d a c p (r ≫ (Ot).ι)
    (by simpa only [nodalShallowCommonInput_fst_contraction] using ha)
    (by simpa only [nodalShallowCommonInput_snd_contraction] using hc)
  rw [← Category.assoc,
    tripleCommonOutput_local D data hk a c j hj hkj true q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    tripleAdditionOutput, tripleTangentGluedOutput_contraction]

/-- The shallow law agrees with the constructed exact-triple output on a secant refinement. -/
theorem tripleCommonOutput_shallowLocalSecant {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Os).toScheme) [Flat r]
    (hpq : p ≫ shallowPair = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc false) :
    p ≫ shallowOut =
      q ≫ tripleCommonOutput D data hk a c j hj hkj := by
  have ha : p ≫ shallowPair ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      tripleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [tripleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ shallowPair ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      tripleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [tripleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply nodalShallowCommonOutput_crossDepthSecantOverlap D hs hsm data hsn d' a' c'
    j hj hsj d a c p (r ≫ (Os).ι)
    (by simpa only [nodalShallowCommonInput_fst_contraction] using ha)
    (by simpa only [nodalShallowCommonInput_snd_contraction] using hc)
  rw [← Category.assoc,
    tripleCommonOutput_local D data hk a c j hj hkj false q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    tripleAdditionOutput, tripleSecantGluedOutput_contraction]

/-- Every flat refinement of the entire exact-triple/shallow overlap has equal outputs. -/
theorem tripleCommonOutput_shallowOverlap {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ shallowPair = q ≫ pair) :
    p ≫ shallowOut =
      q ≫ tripleCommonOutput D data hk a c j hj hkj := by
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
    exact tripleCommonOutput_shallowLocalSecant D data hk a c
      j hj hkj hs hsm hsn d' a' c' hlj hsj (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact tripleCommonOutput_shallowLocalTangent D data hk a c
      j hj hkj hs hsm hsn d' a' c' hlj hsj (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth

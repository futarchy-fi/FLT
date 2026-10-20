/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowCommonFormula
public import FLT.Mazur.WeierstrassDividedCrossDepthResolvedTangentTangent
public import FLT.Mazur.WeierstrassDividedCrossDepthResolvedTangentSecant

/-!
# The entire shallow overlap with the resolved tangent law

Cross-depth comparisons identify both local formulas, and the pulled-back
shallow cover extends the equality to the full common source.
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

local notation "V" => nodalShallowSmoothSourceOpen D hdepth hm data hr d a c
local notation "src" => nodalShallowAdditionSource D hdepth hm data hr d a c
local notation "inc" => nodalShallowAdditionInclusion D hdepth hm data hr d a c
local notation "out" => nodalShallowAdditionOutput D hdepth hm data hr d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data (m - 2 * k) j hrj hj

local notation "Ot" => nodalShallowTangentBranchOutputOpen D hdepth hm data hr d a c
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "Rcp" => finiteResolvedTangentOutputOpen hπ data j hj
local notation "pair" => nodalShallowCommonInput D hdepth hm data hr d a c j hj hkj

local notation "Os" => ⨆ i, nodalShallowSecantLocalOpen D hdepth hm data hr d a c i
local notation "E" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "es" => IsScalarTower.toAlgHom R S E

/-- The tangent law agrees with the constructed shallow output on a tangent refinement. -/
theorem nodalShallowCommonOutput_tangentLocalTangent {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ finiteResolvedTangentDomainMap hπ data j hj = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc true) :
    p ≫ finiteResolvedTangentAddition hπ data j hj =
      q ≫ nodalShallowCommonOutput D hdepth hm data hr d a c j hj hrj := by
  have ha : p ≫ finiteResolvedTangentDomainMap hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      nodalShallowCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalShallowAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ finiteResolvedTangentDomainMap hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      nodalShallowCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalShallowAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply finiteResolvedTangent_crossDepthTangentOverlap hπ data j hj d a c
    p (r ≫ (Ot).ι) ha hc
  rw [← Category.assoc,
    nodalShallowCommonOutput_local D hdepth hm data hr d a c j hj hrj true q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    nodalShallowAdditionOutput, nodalShallowTangentGluedOutput_contraction]

/-- The tangent law agrees with the constructed shallow output on a secant refinement. -/
theorem nodalShallowCommonOutput_tangentLocalSecant {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Os).toScheme) [Flat r]
    (hpq : p ≫ finiteResolvedTangentDomainMap hπ data j hj = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc false) :
    p ≫ finiteResolvedTangentAddition hπ data j hj =
      q ≫ nodalShallowCommonOutput D hdepth hm data hr d a c j hj hrj := by
  have ha : p ≫ finiteResolvedTangentDomainMap hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      nodalShallowCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalShallowAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ finiteResolvedTangentDomainMap hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Os).ι) ≫ Spec.map (CommRingCat.ofHom ((es).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      nodalShallowCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalShallowAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply finiteResolvedTangent_crossDepthSecantOverlap hπ data j hj d a c
    p (r ≫ (Os).ι) ha hc
  rw [← Category.assoc,
    nodalShallowCommonOutput_local D hdepth hm data hr d a c j hj hrj false q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    nodalShallowAdditionOutput, nodalShallowSecantGluedOutput_contraction]

/-- Every flat refinement of the entire shallow/tangent overlap has equal outputs. -/
theorem nodalShallowCommonOutput_tangentOverlap {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme) [Flat q]
    (hpq : p ≫ finiteResolvedTangentDomainMap hπ data j hj = q ≫ pair) :
    p ≫ finiteResolvedTangentAddition hπ data j hj =
      q ≫ nodalShallowCommonOutput D hdepth hm data hr d a c j hj hrj := by
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
  have hp : (f ≫ p) ≫ finiteResolvedTangentDomainMap hπ data j hj =
      (f ≫ q) ≫ pair := by rw [Category.assoc, hpq, Category.assoc]
  cases b with
  | false =>
    exact nodalShallowCommonOutput_tangentLocalSecant D hdepth hm data hr d a c
      j hj hkj hrj (f ≫ p) (f ≫ q) r hp he
  | true =>
    exact nodalShallowCommonOutput_tangentLocalTangent D hdepth hm data hr d a c
      j hj hkj hrj (f ≫ p) (f ≫ q) r hp he

end FLT.Mazur.WeierstrassDividedDepth

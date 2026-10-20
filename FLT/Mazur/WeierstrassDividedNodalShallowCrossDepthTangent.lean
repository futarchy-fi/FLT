/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowCommonFormula
public import FLT.Mazur.WeierstrassDividedDataFormulaComparison

/-!
# Compare the full shallow law with a formula at another depth

Pull back the entire shallow tangent/secant cover. Equality of original inputs
compares each actual formula and hence the entire constructed output.
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

variable {l : ℕ} (d' : Data W π l)
  (a' c' : Coordinate W (π ^ l) d'.b3 d'.b4 d'.b6 →ₐ[R] S')
local notation "Q" => DividedTangentRing W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
local notation "e'" => IsScalarTower.toAlgHom R S' Q
local notation "formula" => dividedTangentToCurve W (π ^ l) d'.b3 d'.b4 d'.b6 a' c'
  d'.factor3 d'.factor4 d'.factor6

/-- Matching original inputs determine the shallow contraction on its entire domain. -/
theorem nodalShallowCommonOutput_crossDepthTangentOriginal {X : Scheme}
    (p : X ⟶ (V).toScheme) (q : X ⟶ Spec (.of Q)) [Flat q]
    (ha : p ≫ (V).ι ≫ Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d =
      q ≫ Spec.map (CommRingCat.ofHom ((e').comp a').toRingHom) ≫ toCurve d')
    (hc : p ≫ (V).ι ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫ toCurve d =
      q ≫ Spec.map (CommRingCat.ofHom ((e').comp c').toRingHom) ≫ toCurve d') :
    p ≫ nodalShallowCommonOutput D hdepth hm data hr d a c j hj hrj ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj = q ≫ formula := by
  let v := Scheme.homOfLE (Spec (.of S)) (show V ≤ O from inf_le_left)
  apply Scheme.Cover.hom_ext ((C).pullback₁ (p ≫ v))
  intro b
  let f := pullback.fst (p ≫ v) ((C).f b)
  let g := pullback.snd (p ≫ v) ((C).f b)
  let r := g ≫ (inc b).isoOpensRange.inv
  have hp : f ≫ p ≫ v = g ≫ (C).f b := pullback.condition
  have hi : (C).f b ≫ (O).ι = (inc b).opensRange.ι :=
    Scheme.homOfLE_ι _ (le_iSup (fun i => (inc i).opensRange) b)
  have he : (f ≫ p) ≫ (V).ι = r ≫ inc b := by
    have h := congrArg (· ≫ (O).ι) hp
    simpa only [r, v, Category.assoc, hi, Scheme.homOfLE_ι,
      Scheme.Hom.isoOpensRange_inv_comp] using h
  have hl : r ≫ inc b ≫ Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d =
      (f ≫ q) ≫ Spec.map (CommRingCat.ofHom ((e').comp a').toRingHom) ≫ toCurve d' := by
    rw [← Category.assoc, ← he]
    simpa only [Category.assoc] using congrArg (f ≫ ·) ha
  have hr' : r ≫ inc b ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫ toCurve d =
      (f ≫ q) ≫ Spec.map (CommRingCat.ofHom ((e').comp c').toRingHom) ≫ toCurve d' := by
    rw [← Category.assoc, ← he]
    simpa only [Category.assoc] using congrArg (f ≫ ·) hc
  have ho := nodalShallowCommonOutput_local D hdepth hm data hr d a c j hj hrj
    b (f ≫ p) r he
  have hout := congrArg (· ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj) ho
  simp only [Category.assoc] at hout
  change f ≫ p ≫ _ = f ≫ q ≫ _
  rw [hout]
  cases b with
  | false =>
    simp only [finiteGlobalSmoothTransition_contraction, nodalShallowAdditionOutput,
      nodalShallowSecantGluedOutput_contraction]
    have h := dividedDataSecantTangent_compare hπ d d' a c a' c'
      (r ≫ (⨆ i, nodalShallowSecantLocalOpen D hdepth hm data hr d a c i).ι) (f ≫ q)
      (by simpa only [nodalShallowAdditionInclusion, Category.assoc,
            AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
            Spec.map_comp, IsScalarTower.coe_toAlgHom] using hl)
      (by simpa only [nodalShallowAdditionInclusion, Category.assoc,
            AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
            Spec.map_comp, IsScalarTower.coe_toAlgHom] using hr')
    simpa only [Category.assoc] using h
  | true =>
    simp only [finiteGlobalSmoothTransition_contraction, nodalShallowAdditionOutput,
      nodalShallowTangentGluedOutput_contraction]
    have h := dividedDataTangentTangent_compare hπ d d' a c a' c'
      (r ≫ (nodalShallowTangentBranchOutputOpen D hdepth hm data hr d a c).ι) (f ≫ q)
      (by simpa only [nodalShallowAdditionInclusion, Category.assoc,
            AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
            Spec.map_comp, IsScalarTower.coe_toAlgHom] using hl)
      (by simpa only [nodalShallowAdditionInclusion, Category.assoc,
            AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp,
            Spec.map_comp, IsScalarTower.coe_toAlgHom] using hr')
    simpa only [Category.assoc] using h

/-- The shallow law equals any constructed finite-model lift of the matching formula. -/
theorem nodalShallowCommonOutput_crossDepthTangentOverlap {X : Scheme}
    (p : X ⟶ (V).toScheme) (q : X ⟶ Spec (.of Q)) [Flat q]
    (ha : p ≫ (V).ι ≫ Spec.map (CommRingCat.ofHom a.toRingHom) ≫ toCurve d =
      q ≫ Spec.map (CommRingCat.ofHom ((e').comp a').toRingHom) ≫ toCurve d')
    (hc : p ≫ (V).ι ≫ Spec.map (CommRingCat.ofHom c.toRingHom) ≫ toCurve d =
      q ≫ Spec.map (CommRingCat.ofHom ((e').comp c').toRingHom) ≫ toCurve d')
    (z : X ⟶ (U).toScheme)
    (hz : z ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj = q ≫ formula) :
    p ≫ nodalShallowCommonOutput D hdepth hm data hr d a c j hj hrj = z := by
  apply (cancel_mono (U).ι).mp
  apply finiteTangentOutput_ext hπ data hj d' a' c' q
  · simpa only [Category.assoc] using
      nodalShallowCommonOutput_crossDepthTangentOriginal D hdepth hm data hr d a c
        j hj hrj d' a' c' p q ha hc
  · simpa only [Category.assoc] using hz

end FLT.Mazur.WeierstrassDividedDepth

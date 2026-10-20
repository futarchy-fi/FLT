/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateCommonFormula
public import FLT.Mazur.WeierstrassDividedCrossDepthResolvedReciprocalSecant

/-!
# Intermediate secant compatibility with the resolved reciprocal law

The two laws have the same original inputs on each local intermediate secant
refinement. Cross-depth comparison identifies their actual finite-model outputs.
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

local notation "V" => nodalIntermediateSmoothSourceOpen D hdepth hrk hrm data hr d a c
local notation "src" => nodalIntermediateAdditionSource D hdepth hrk hrm data hr d a c
local notation "inc" => nodalIntermediateAdditionInclusion D hdepth hrk hrm data hr d a c
local notation "out" => nodalIntermediateAdditionOutput D hdepth hrk hrm data hr d a c
local notation "C" => Scheme.Opens.iSupOpenCover (fun i => (inc i).opensRange)
local notation "promote" => finiteGlobalSmoothTransition hπ data (k + r) j hrj hj

local notation "Ot" => ⨆ i, nodalIntermediateSecantLocalOpen D hdepth hrk hrm data hr d a c i
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "Rcp" => finiteResolvedReciprocalOutputOpen hπ data j hj
local notation "pair" => nodalIntermediateCommonInput D hdepth hrk hrm data hr d a c j hj hkj

/-- The reciprocal law agrees with the constructed intermediate output on a secant refinement. -/
theorem nodalIntermediateCommonOutput_reciprocalSecant {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc false) :
    p ≫ finiteResolvedReciprocalAddition hπ data j hj =
      q ≫ nodalIntermediateCommonOutput D hdepth hrk hrm data hr d a c j hj hrj := by
  have ha : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      nodalIntermediateCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [nodalIntermediateAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      nodalIntermediateCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [nodalIntermediateAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply finiteResolvedReciprocal_crossDepthSecantOverlap hπ data j hj d a c
    p (r ≫ (Ot).ι) ha hc
  rw [← Category.assoc,
    nodalIntermediateCommonOutput_local D hdepth hrk hrm data hr d a c j hj hrj false q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    nodalIntermediateAdditionOutput, nodalIntermediateSecantGluedOutput_contraction]

end FLT.Mazur.WeierstrassDividedDepth

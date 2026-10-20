/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleCommonFormula
public import FLT.Mazur.WeierstrassDividedCrossDepthResolvedReciprocalTangent

/-!
# Exact-triple tangent compatibility with the resolved reciprocal law

The two laws have the same original inputs on each local exact-triple tangent
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
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
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
local notation "T" => DividedTangentRing W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c
local notation "e" => IsScalarTower.toAlgHom R S T
local notation "Rcp" => finiteResolvedReciprocalOutputOpen hπ data j hj
local notation "pair" => tripleCommonInput D data hk a c j hj hkj

/-- The reciprocal law agrees with the constructed exact-triple output on a tangent refinement. -/
theorem tripleCommonOutput_reciprocalTangent {X : Scheme}
    (p : X ⟶ (Rcp).toScheme) (q : X ⟶ (V).toScheme)
    (r : X ⟶ (Ot).toScheme) [Flat r]
    (hpq : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj = q ≫ pair)
    (hqr : q ≫ (V).ι = r ≫ inc true) :
    p ≫ finiteResolvedReciprocalAddition hπ data j hj =
      q ≫ tripleCommonOutput D data hk a c j hj hkj := by
  have ha : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.fst t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp a).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      tripleCommonInput_fst_contraction, ← Category.assoc, hqr]
    simp only [tripleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  have hc : p ≫ finiteResolvedReciprocalDomainMap hπ data j hj ≫ pullback.snd t t ≫
        (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (r ≫ (Ot).ι) ≫ Spec.map (CommRingCat.ofHom ((e).comp c).toRingHom) ≫
        toCurve d := by
    rw [← Category.assoc, hpq, Category.assoc,
      tripleCommonInput_snd_contraction, ← Category.assoc, hqr]
    simp only [tripleAdditionInclusion, Category.assoc,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, IsScalarTower.coe_toAlgHom]
  apply finiteResolvedReciprocal_crossDepthTangentOverlap hπ data j hj d a c
    p (r ≫ (Ot).ι) ha hc
  rw [← Category.assoc,
    tripleCommonOutput_local D data hk a c j hj hkj true q r hqr]
  simp only [Category.assoc, finiteGlobalSmoothTransition_contraction,
    tripleAdditionOutput, tripleTangentGluedOutput_contraction]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationSectionFamilies
public import FLT.Mazur.PolygonLineHZero
/-!
# Actual polygon H0 and weighted polynomial matching

The intrinsic normalization kernel is equivalent to the existing weighted
polynomial matching space. The map is the actual normalization pullback,
component restriction and polynomial coordinate. This is an equivalence of
types; no linearity of the assembled equivalence is asserted here.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonPowerBranchValues
open FCurve PolygonPinching ProjectiveLineMarkedHZero
open PolygonPowerNodeEndpoints LinePullbackRestriction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (m : ℕ)
/-- Actual H0 of the direct image from the normalization. -/
abbrev normalizationH0 := ModuleScalarH C.hom
  ((pushforward p.left).obj (normalizationLine K n hn p q h a m)) 0
/-- The divisor power is locally free of rank one. -/
abbrev lineFree :=
  ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m).divisorLineBundle_locallyFreeRankOne
/-- The intrinsic H0 kernel is detected by equality at each actual node. -/
lemma kernel_iff_nodeValues (x : normalizationH0 K n hn p q h a m) :
    moduleScalarHMap C.hom (PolygonLineNormalization.complex K n hn p q h
      (polygonLine K n hn p q h a m) (lineFree K n hn p q h a m)).g 0 x = 0 ↔
    ∀ i, nodeValue K n hn p q h a m false i
      (moduleScalarH0Equiv C.hom _ x) =
      nodeValue K n hn p q h a m true i (moduleScalarH0Equiv C.hom _ x) := by
  rw [PolygonLineHZero.matching_iff]
  constructor
  · intro he
    have hs := congrArg (moduleScalarH0Equiv C.hom
      ((pushforward q.left).obj ((Scheme.Modules.pullback q.left).obj
        (polygonLine K n hn p q h a m)))) he
    simp only [moduleScalarH0Equiv_naturality] at hs
    intro i
    exact congrArg (fun s ↦ (sealedAlong (nodeι K n i).left q.left
      (nodeι K n i ≫ q).left rfl (polygonLine K n hn p q h a m)).app ⊤ s) hs
  · intro he
    apply (moduleScalarH0Equiv C.hom _).injective
    rw [moduleScalarH0Equiv_naturality, moduleScalarH0Equiv_naturality]
    apply nodeRestriction_injective K n q (polygonLine K n hn p q h a m)
    exact funext he

/-- Every normalization H0 class is uniquely represented by component polynomials. -/
def normalizationPolynomialEquiv : normalizationH0 K n hn p q h a m ≃
    (∀ _ : Fin n, Polynomial.degreeLT K (m + 1)) :=
  (moduleScalarH0Equiv C.hom _).toEquiv.trans
    ((Equiv.ofBijective (componentClass K n hn p q h a m)
      (componentClass_bijective K n hn p q h a m)).trans
        (Equiv.piCongrRight (fun i ↦ (polynomialEquiv K (a i) m).toEquiv)))
/-- Intrinsic kernel membership is precisely weighted polynomial matching. -/
lemma kernel_iff_polynomial (d : ℕ) (x : normalizationH0 K n hn p q h a (d + 1)) :
    moduleScalarHMap C.hom (PolygonLineNormalization.complex K n hn p q h
      (polygonLine K n hn p q h a (d + 1)) (lineFree K n hn p q h a (d + 1))).g 0 x = 0 ↔
    normalizationPolynomialEquiv K n hn p q h a (d + 1) x ∈
      PolygonPolynomialMatching.matching (fun _ : Fin n ↦ d) (finRotate n).symm
        (weight K n a (d + 1)) :=
  (kernel_iff_nodeValues K n hn p q h a (d + 1) x).trans
    (polynomial_matching_iff K n hn p q h a d (moduleScalarH0Equiv C.hom _ x))
/-- Actual polygon H0 is equivalent to the existing weighted matching space. -/
def h0PolynomialEquiv (d : ℕ) :
    ModuleScalarH C.hom (polygonLine K n hn p q h a (d + 1)) 0 ≃
      PolygonPolynomialMatching.matching (fun _ : Fin n ↦ d) (finRotate n).symm
        (weight K n a (d + 1)) :=
  (PolygonLineHZero.kernelEquiv K n hn p q h (polygonLine K n hn p q h a (d + 1))
    (lineFree K n hn p q h a (d + 1))).toEquiv.trans
      ((normalizationPolynomialEquiv K n hn p q h a (d + 1)).subtypeEquiv
        (kernel_iff_polynomial K n hn p q h a d))
/-- The polynomial equivalence retains the actual normalization pullback map. -/
lemma h0PolynomialEquiv_val (d : ℕ)
    (x : ModuleScalarH C.hom (polygonLine K n hn p q h a (d + 1)) 0) :
    (h0PolynomialEquiv K n hn p q h a d x).val =
      normalizationPolynomialEquiv K n hn p q h a (d + 1)
        (moduleScalarHMap C.hom ((pullbackPushforwardAdjunction p.left).unit.app
          (polygonLine K n hn p q h a (d + 1))) 0 x) :=
  congrArg (normalizationPolynomialEquiv K n hn p q h a (d + 1))
    (PolygonLineHZero.kernelEquiv_val K n hn p q h (polygonLine K n hn p q h a (d + 1))
      (lineFree K n hn p q h a (d + 1)) x)
end FLT.Mazur.PolygonPowerBranchValues

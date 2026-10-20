/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleSecantGluing
public import FLT.Mazur.WeierstrassDividedGlobalSmoothTransition
public import FLT.Mazur.WeierstrassDividedNodalInputSmoothVertical
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothPair

/-!
# Promote the exact-triple secant law with full relative-smooth input coverage

The original three-output secant union moves to any supplied later stage.
Its complete cubic formula and coefficient map are unchanged. On the nodal
fiber, full relative smoothness supplies both vertical derivative conditions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "T" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "U" => (finiteGlobalStructure hπ data k hk).smoothLocus
local notation "sec" => dividedSecantToCurve W s (d).b3 (d).b4 (d).b6 a c
  (d).factor3 (d).factor4 (d).factor6
local notation "inc" => tripleSecantNeighborhoodInclusion D data hk a c

local notation "O" => ⨆ i, tripleSecantLocalOpen D data hk a c i
local notation "e" => IsScalarTower.toAlgHom R S T
variable (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "Q" => (base).smoothLocus
local notation "promote" => finiteGlobalSmoothTransition hπ data k j hkj hj

/-- The entire constructed exact-triple secant law in a later common finite model. -/
def triplePromotedSecantOutput : (O).toScheme ⟶ (Q).toScheme :=
  tripleSecantGluedOutput D data hk a c ≫ promote

/-- Promotion retains the complete original cubic secant formula. -/
@[reassoc] theorem triplePromotedSecantOutput_contraction :
    triplePromotedSecantOutput D data hk a c j hj hkj ≫ (Q).ι ≫
        finiteGlobalContraction hπ data j hj = (O).ι ≫ sec := by
  rw [triplePromotedSecantOutput, Category.assoc, finiteGlobalSmoothTransition_contraction,
    tripleSecantGluedOutput_contraction]

/-- The exact-triple output retains its original coefficient point. -/
@[reassoc] theorem triplePromotedSecantOutput_structure :
    triplePromotedSecantOutput D data hk a c j hj hkj ≫ (Q).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (Q).ι ≫ finiteGlobalContraction hπ data j hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [triplePromotedSecantOutput_contraction_assoc, dividedSecantToCurve_structure]

/-- Every original local formula is preserved in the chosen common target. -/
@[reassoc] theorem triplePromotedSecantOutput_restrict (i : Option Bool) :
    (Scheme.Opens.iSupOpenCover
        (tripleSecantLocalOpen D data hk a c)).f i ≫
          triplePromotedSecantOutput D data hk a c j hj hkj =
      tripleSecantLocalOutput D data hk a c i ≫ promote := by
  rw [triplePromotedSecantOutput, tripleSecantGluedOutput_restrict_assoc]

/-- Both full relatively smooth inputs give exact-triple secant coverage on the nodal fiber. -/
theorem tripleSecantGluedOutput_relativeSmooth (hpos : 0 < start + k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (hs : p ∈ suppliedDividedSmoothInputOpen d ((e).comp a) ((e).comp c)) : p ∈ O := by
  have hlo : 2 * (start + k) < 3 * (start + k) := by omega
  apply tripleSecantGluedOutput_covers D data hk a c p hp
  · exact nodalDividedInput_smooth_vertical D d ((e).comp a) hpos hlo p hp hs.1
  · exact nodalDividedInput_smooth_vertical D d ((e).comp c) hpos hlo p hp hs.2

end FLT.Mazur.WeierstrassDividedDepth

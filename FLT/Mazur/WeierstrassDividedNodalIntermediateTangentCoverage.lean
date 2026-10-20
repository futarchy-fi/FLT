/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateNegativeBranchOutput
public import FLT.Mazur.WeierstrassDividedTangentThreeDomainCover
public import FLT.Mazur.WeierstrassDividedTangentReverseScheme

/-!
# Smooth intermediate outputs cover tangent points off the secant domain

The complementary and swapped strict branches supply actual smooth
outputs over every closed-fiber tangent point whose two divided abscissae
coincide. More generally these outputs and the secant domain cover every
tangent point, without assuming an original second-coefficient normalization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalIntermediateBranchCommonOutput nodalIntermediateNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ}
  (D : SplitNodeDepth W π m) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W (π ^ k) (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W (π ^ k) (d).b3 (d).b4 (d).b6 c
local notation "N" => DividedShearBranchOverlap W (π ^ k) (d).b3 (d).b4 (d).b6 σ a' c'
local notation "B" => DividedShearBranchOverlap W (π ^ k) (d).b3 (d).b4 (d).b6 σ c a
local notation "base" => finiteGlobalStructure D.uniformizer_ne_zero
  (start := 0) data (k + r) hj
local notation "dx" =>
  a (x W (π ^ k) (d).b3 (d).b4 (d).b6) - c (x W (π ^ k) (d).b3 (d).b4 (d).b6)

/-- The swapped actual output still contracts to tangent addition in the original input order. -/
theorem nodalIntermediateSwappedBranchOutput_original_contraction {X : Scheme}
    (p : X ⟶ Spec (.of B))
    (q : X ⟶ Spec (.of (DividedTangentRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c)))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      q ≫ Spec.map (CommRingCat.ofHom
        (algebraMap S (DividedTangentRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c)))) :
    p ≫ nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d c a ≫
        finiteGlobalContraction D.uniformizer_ne_zero data
          (k + r) hj =
      q ≫ dividedTangentToCurve W (π ^ k) (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  let f := dividedShearBranchOverlapOriginal W (π ^ k) (d).b3 (d).b4 (d).b6 σ c a
  let T := DividedTangentRing W (π ^ k) (d).b3 (d).b4 (d).b6 c a
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact dividedShearBranchOverlapOriginal_source W (π ^ k) (d).b3 (d).b4 (d).b6 σ c a z
  have hout := dividedTangentReverse_scheme W (π ^ k) (d).b3 (d).b4 (d).b6 c a
    (d).factor3 (d).factor4 (d).factor6 (p ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) q
    (by rw [Category.assoc, hf, hpq])
  simpa only [nodalIntermediateBranchCommonOutput_contraction, Category.assoc] using hout

variable [IsNoetherianRing R]

/-- Actual complementary and swapped outputs cover every tangent prime outside the secant open. -/
theorem nodalIntermediateTangent_smooth_branch_or_secant
    (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ht : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a c)) :
    p ∈ PrimeSpectrum.basicOpen dx ∨
      (∃ q : PrimeSpectrum N, PrimeSpectrum.comap (algebraMap S N) q = p ∧
        algebraMap R N π ∈ q.asIdeal ∧
          nodalIntermediateNegativeBranchOutput D hdepth hrk hrm data hj d a c q ∈
          (base).smoothLocus) ∨
      (∃ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap S B) q = p ∧
        algebraMap R B π ∈ q.asIdeal ∧
          nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d c a q ∈
          (base).smoothLocus) := by
  rcases dividedTangent_three_domains W (π ^ k)
    (d).b3 (d).b4 (d).b6 a c p ht with hx | hn | hb
  · exact Or.inl hx
  · exact Or.inr (Or.inl (nodalIntermediateNegativeBranchOutput_covers
      D hdepth hrk hrm data hj d a c hm hr p hp hn))
  · exact Or.inr (Or.inr (nodalIntermediateBranchCommonOutput_covers
      D hdepth hrk hrm data hj d c a hm hr p hp hb))

/-- Coincident divided abscissae on the closed fiber always have a constructed smooth output. -/
theorem nodalIntermediateTangent_equal_abscissae_smooth
    (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ht : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ k)
        (d).b3 (d).b4 (d).b6 a c)) (hx : dx ∈ p.asIdeal) :
    (∃ q : PrimeSpectrum N, PrimeSpectrum.comap (algebraMap S N) q = p ∧
      algebraMap R N π ∈ q.asIdeal ∧
        nodalIntermediateNegativeBranchOutput D hdepth hrk hrm data hj d a c q ∈
          (base).smoothLocus) ∨
    (∃ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap S B) q = p ∧
      algebraMap R B π ∈ q.asIdeal ∧
        nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d c a q ∈
          (base).smoothLocus) := by
  rcases nodalIntermediateTangent_smooth_branch_or_secant
    D hdepth hrk hrm data hj d a c hm hr p hp ht with hs | h
  · exact (hs hx).elim
  · exact h

end FLT.Mazur.WeierstrassDividedDepth

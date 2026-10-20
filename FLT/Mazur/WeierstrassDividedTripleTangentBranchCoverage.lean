/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleNegativeBranchOutput
public import FLT.Mazur.WeierstrassDividedTangentThreeDomainCover
public import FLT.Mazur.WeierstrassDividedTangentReverseScheme

/-!
# Smooth finite outputs cover tangent points off the secant domain

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
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : WeierstrassDilatation.Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "r" => nodalSecondShear D (start + k)
local notation "a'" => branchNegativeInput W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 c
local notation "N" => DividedShearBranchOverlap W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a' c'
local notation "B" => DividedShearBranchOverlap W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r c a
local notation "base" => finiteGlobalStructure D.uniformizer_ne_zero
  data k hk
local notation "dx" =>
  a (x W (π ^ (start + k)) (d).b3 (d).b4 (d).b6) - c (x W (π ^ (start + k)) (d).b3 (d).b4 (d).b6)

/-- The swapped actual output still contracts to tangent addition in the original input order. -/
theorem tripleSwappedBranchOutput_original_contraction {X : Scheme}
    (p : X ⟶ Spec (.of B))
    (q : X ⟶ Spec (.of (DividedTangentRing W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c)))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      q ≫ Spec.map (CommRingCat.ofHom
        (algebraMap S (DividedTangentRing W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c)))) :
    p ≫ tripleBranchCommonOutput D data hk c a ≫
        finiteGlobalContraction D.uniformizer_ne_zero data
          k hk =
      q ≫ dividedTangentToCurve W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  let f := dividedShearBranchOverlapOriginal W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r c a
  let T := DividedTangentRing W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 c a
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact dividedShearBranchOverlapOriginal_source W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r c a z
  have hout := dividedTangentReverse_scheme W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 c a
    (d).factor3 (d).factor4 (d).factor6 (p ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) q
    (by rw [Category.assoc, hf, hpq])
  simpa only [tripleBranchCommonOutput_contraction, Category.assoc] using hout

variable [IsNoetherianRing R]

/-- Actual complementary and swapped outputs cover every tangent prime outside the secant open. -/
theorem tripleTangent_smooth_branch_or_secant (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ht : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c)) :
    p ∈ PrimeSpectrum.basicOpen dx ∨
      (∃ q : PrimeSpectrum N, PrimeSpectrum.comap (algebraMap S N) q = p ∧
        algebraMap R N π ∈ q.asIdeal ∧
          tripleNegativeBranchOutput D data hk a c q ∈ (base).smoothLocus) ∨
      (∃ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap S B) q = p ∧
        algebraMap R B π ∈ q.asIdeal ∧
          tripleBranchCommonOutput D data hk c a q ∈ (base).smoothLocus) := by
  rcases dividedTangent_three_domains W (π ^ (start + k))
    (d).b3 (d).b4 (d).b6 a c p ht with hx | hn | hb
  · exact Or.inl hx
  · exact Or.inr (Or.inl (tripleNegativeBranchOutput_covers D data hk a c p hp hn))
  · exact Or.inr (Or.inr (tripleBranchCommonOutput_covers D data hk c a p hp hb))

/-- Coincident divided abscissae on the closed fiber always have a constructed smooth output. -/
theorem tripleTangent_equal_abscissae_smooth (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ht : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ (start + k))
        (d).b3 (d).b4 (d).b6 a c)) (hx : dx ∈ p.asIdeal) :
    (∃ q : PrimeSpectrum N, PrimeSpectrum.comap (algebraMap S N) q = p ∧
      algebraMap R N π ∈ q.asIdeal ∧
        tripleNegativeBranchOutput D data hk a c q ∈ (base).smoothLocus) ∨
    (∃ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap S B) q = p ∧
      algebraMap R B π ∈ q.asIdeal ∧
        tripleBranchCommonOutput D data hk c a q ∈ (base).smoothLocus) := by
  rcases tripleTangent_smooth_branch_or_secant D data hk a c p hp ht with hs | h
  · exact (hs hx).elim
  · exact h

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeSumDepthOutput
public import FLT.Mazur.WeierstrassDividedUnequalDepthCoverage
public import FLT.Mazur.WeierstrassDividedPreMiddleBranchDichotomy

/-!
# Three actual output domains cover punctured unequal divided inputs

This coverage is independent of the source atlas presentation. It can therefore
be pulled back along the exact own-depth coordinates of successive tensor pairs.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m n : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : k + l ≤ n)
  (dd : Data W π (k + k)) (ee : Data W π (l + l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (b : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => b (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₂" => b (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "α" => algebraMap R S W.a₁
local notation "C₁" => dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a
local notation "C₂" => dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 b

/-- The three constructed domains cover without a chosen branch or denominator premise. -/
theorem puncturedUnequalDomain_cover (hk : 0 < k) (hlt : k < l) (hm : 2 * (k + l) < m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : x₁ ∉ p.asIdeal) (hu : x₂ ∉ p.asIdeal) :
    p ∈ sumDepthDomain hπ d e hkl data hd dd ee h2 a b ∨
    p ∈ negativeSumDepthDomain hπ d e hkl data hd dd ee h2 a b ∨
    p ∈ unequalDepthDomain hπ d e hkl data (by omega : l - k ≤ n) a b := by
  have hkm : 2 * k < m := by omega
  have hlm : 2 * l < m := by omega
  have hb₁ := preMiddleInput_branch_dichotomy D d a hk hkm p hp
  have hb₂ := preMiddleInput_branch_dichotomy D e b (by omega) hlm p hp
  have h3₁ := preMiddleInput_b3_mem D d hkm p hp
  have h3₂ := preMiddleInput_b3_mem D e hlm p hp
  have neg₁ (h : C₁ ∈ p.asIdeal) : y₁ + α * x₁ ∈ p.asIdeal := by
    simpa only [dividedTangentBranchFactor, add_sub_cancel_right] using p.asIdeal.sub_mem h h3₁
  have neg₂ (h : C₂ ∈ p.asIdeal) : y₂ + α * x₂ ∈ p.asIdeal := by
    simpa only [dividedTangentBranchFactor, add_sub_cancel_right] using p.asIdeal.sub_mem h h3₂
  rcases hb₁ with hy | hy <;> rcases hb₂ with hv | hv
  · exact Or.inl (sumDepthDomain_positive_mem D d e hkl data hd dd ee h2 a b
      hk hlt hm p hp hx hu hy hv)
  · exact Or.inr (Or.inr (unequalDepthDomain_opposite_mem D d e hkl data (by omega) a b
      hk hlt hlm p hp hx hu (Or.inl ⟨hy, neg₂ hv⟩)))
  · exact Or.inr (Or.inr (unequalDepthDomain_opposite_mem D d e hkl data (by omega) a b
      hk hlt hlm p hp hx hu (Or.inr ⟨neg₁ hy, hv⟩)))
  · exact Or.inr (Or.inl (negativeSumDepthDomain_mem hπ d e hkl data hd dd ee h2 a b
      D hk hlt hm p hp hx hu hy hv))

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalWiderReflectedBoundary
public import FLT.Mazur.WeierstrassDividedNodalWiderReflectedPuncturedCover

/-!
# Both branch signs through the upper wider boundary

The same positive and negative source opens cover the closed wider interval.
Together with the existing opposite formula they cover every punctured pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m n : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hd : m - k - l ≤ n)
  (hm : k + 2 * l ≤ m) (htop : m ≤ 2 * (k + l))
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ l) e.b3 e.b4 e.b6 c

/-- Negative punctured branches have actual smooth outputs on the unchanged full input spectrum. -/
theorem nodalWiderReflectedNegativeDomain_le_top_mem (hk : 0 < k) (hlt : k < l)
    (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ l) e.b3 e.b4 e.b6) ∉ p.asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a ∈ p.asIdeal)
    (hv : dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c ∈ p.asIdeal) :
    p ∈ nodalWiderReflectedNegativeDomain D d e hkl data hd hm htop a c := by
  apply nodalWiderReflectedDomain_le_top_positive_mem D d e hkl data hd hm htop
    a' c' hk hlt p hp
  · simpa only [branchNegativeInput_x] using hx
  · simpa only [branchNegativeInput_x] using hu
  · have he : a' (y W (π ^ k) d.b3 d.b4 d.b6) =
        -dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a := by
      rw [branchNegativeInput_y, dividedTangentBranchFactor]
      ring
    rw [he]
    exact p.asIdeal.neg_mem hy
  · have he : c' (y W (π ^ l) e.b3 e.b4 e.b6) =
        -dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c := by
      rw [branchNegativeInput_y, dividedTangentBranchFactor]
      ring
    rw [he]
    exact p.asIdeal.neg_mem hv

local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => c (x W (π ^ l) e.b3 e.b4 e.b6)
local notation "y₁" => a (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "y₂" => c (y W (π ^ l) e.b3 e.b4 e.b6)
local notation "α" => algebraMap R S W.a₁
local notation "C₁" => dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a
local notation "C₂" => dividedTangentBranchFactor W (π ^ l) e.b3 e.b4 e.b6 c

/-- The three constructed domains cover without a chosen branch or denominator premise. -/
theorem nodalWiderReflectedPuncturedUnequal_le_top_cover (hk : 0 < k) (hlt : k < l)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : x₁ ∉ p.asIdeal) (hu : x₂ ∉ p.asIdeal) :
    p ∈ nodalWiderReflectedDomain D d e hkl data hd hm htop a c ∨
    p ∈ nodalWiderReflectedNegativeDomain D d e hkl data hd hm htop a c ∨
    p ∈ unequalDepthDomain hπ d e hkl data (by omega : l - k ≤ n) a c := by
  have hkm : 2 * k < m := by omega
  have hlm : 2 * l < m := by omega
  have hb₁ := preMiddleInput_branch_dichotomy D d a hk hkm p hp
  have hb₂ := preMiddleInput_branch_dichotomy D e c (by omega) hlm p hp
  have h3₁ := preMiddleInput_b3_mem D d hkm p hp
  have h3₂ := preMiddleInput_b3_mem D e hlm p hp
  have neg₁ (h : C₁ ∈ p.asIdeal) : y₁ + α * x₁ ∈ p.asIdeal := by
    simpa only [dividedTangentBranchFactor, add_sub_cancel_right] using p.asIdeal.sub_mem h h3₁
  have neg₂ (h : C₂ ∈ p.asIdeal) : y₂ + α * x₂ ∈ p.asIdeal := by
    simpa only [dividedTangentBranchFactor, add_sub_cancel_right] using p.asIdeal.sub_mem h h3₂
  rcases hb₁ with hy | hy <;> rcases hb₂ with hv | hv
  · exact Or.inl (nodalWiderReflectedDomain_le_top_positive_mem D d e hkl data hd hm htop a c
      hk hlt p hp hx hu hy hv)
  · exact Or.inr (Or.inr (unequalDepthDomain_opposite_mem D d e hkl data (by omega) a c
      hk hlt hlm p hp hx hu (Or.inl ⟨hy, neg₂ hv⟩)))
  · exact Or.inr (Or.inr (unequalDepthDomain_opposite_mem D d e hkl data (by omega) a c
      hk hlt hlm p hp hx hu (Or.inr ⟨neg₁ hy, hv⟩)))
  · exact Or.inr (Or.inl (nodalWiderReflectedNegativeDomain_le_top_mem D d e hkl data hd hm htop a c
      hk hlt p hp hx hu hy hv))

end FLT.Mazur.WeierstrassDividedDepth

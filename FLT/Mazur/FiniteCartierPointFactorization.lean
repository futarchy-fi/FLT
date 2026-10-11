/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteDivisorRationalSupport
public import FLT.Mazur.RationalPointProductStalk

/-!
# Full Cartier divisors factor as rational point powers

On a smooth integral curve over an algebraically closed field, every finite
Cartier ideal is the product of powers of its rational support-point ideals.
The equality is equality of entire ideal sheaves, not merely of their supports.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open AnnihilatorSubsheaf
set_option backward.isDefEq.respectTransparency false
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsSeparated f]
  [QuasiCompact f] {I : X.IdealSheafData}

/-- A full finite Cartier ideal is a product of positive rational-point ideal powers. -/
theorem exists_finiteCartier_point_factorization (hI : EffectiveCartier I) :
    ∃ (s : Finset X) (p : s → (Spec (.of k) ⟶ X)) (n : s → ℕ),
      (↑s : Set X) = I.support ∧
      (∀ x, p x ≫ f = 𝟙 _) ∧
      (∀ x, p x (IsLocalRing.closedPoint k) = x.1) ∧
      (∀ x, 0 < n x) ∧ I = ∏ x, (p x).ker ^ n x := by
  classical
  let _ := SmoothOfRelativeDimension.smooth 1 f
  let _ := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := {}
  let _ := hI.isFinite_of_integral_smoothCurve f
  have hd : topologicalKrullDim X ≤ 1 :=
    (smoothCurveDimension f inferInstance inferInstance).le
  let s := (hI.finite_support hd).toFinset
  have hs : (↑s : Set X) = I.support := Set.Finite.coe_toFinset _
  have hs_mem (x : X) : x ∈ s ↔ x ∈ I.support := by
    change x ∈ (↑s : Set X) ↔ x ∈ (I.support : Set X)
    rw [hs]
  have hp : ∀ x : s, ∃ p : Spec (.of k) ⟶ X,
      p ≫ f = 𝟙 _ ∧ p (IsLocalRing.closedPoint k) = x.1 := by
    intro x
    exact finiteDivisor_exists_rationalPoint f I x.1 ((hs_mem x.1).mp x.2)
  choose p hp he using hp
  have hn : ∀ x : s, ∃ n : ℕ, stalkIdeal I x.1 = stalkIdeal (p x).ker x.1 ^ n := by
    intro x
    rw [← he x]
    exact exists_rationalPointIdeal_stalk_pow f (p x) (hp x) hI
  choose n hn using hn
  refine ⟨s, p, n, hs, hp, he, ?_, ?_⟩
  · intro x
    by_contra h
    have hz : n x = 0 := Nat.eq_zero_of_not_pos h
    have hi := (mem_support_iff_stalkIdeal_ne_top I x.1).mp ((hs_mem x.1).mp x.2)
    exact hi (by simpa only [hz, pow_zero, Ideal.one_eq_top] using hn x)
  · apply idealSheaf_eq_of_stalkIdeal_eq
    intro x
    by_cases hx : x ∈ s
    · let z : s := ⟨x, hx⟩
      have hinj : Function.Injective (fun y ↦ p y (IsLocalRing.closedPoint k)) := by
        intro a b hab
        apply Subtype.ext
        simpa only [he] using hab
      have h := rationalPointProduct_stalk f p hp n hinj z
      rw [he z] at h
      exact (hn z).trans h.symm
    · have hi : stalkIdeal I x = 1 := by
        rw [Ideal.one_eq_top, ← not_ne_iff, ← mem_support_iff_stalkIdeal_ne_top]
        exact fun h ↦ hx ((hs_mem x).mpr h)
      rw [hi, rationalPointProduct_stalk_of_notMem f p hp n x]
      intro y h
      exact hx ((h.trans (he y)).symm ▸ y.2)

end FLT.Mazur.FCurve

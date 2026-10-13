/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstInfinityFactorization
public import FLT.Mazur.WeierstrassCoefficientShearInitialAtlasPullback
public import FLT.Mazur.WeierstrassCoefficientShearResidueAtlasAdjacentPullback

/-!
# The full first retained infinity pullback in the coefficient atlas

Transport the entire original vertical tensor boundary through the first retained
shear. The same boundary factors through the complete original initial chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (m : ℕ) (hm : 1 + m ≤ n)
local notation "h1" => show 1 ≤ n from by omega
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, Nat.lt_succ_of_le h1⟩
local notation "y" => successiveOriginalY e
local notation "ci" => incidenceCoefficientShearIso
  W (π ^ start) (d).b3 (d).b4 (d).b6 S r
local notation "cj" => successiveCoefficientShearIso
  W (π ^ (start + 0)) π (e).b3 (e).b4 (e).b6 S r
local notation "atlas" => coefficientShearAtlasMap hπ data S r (1 + m) hm
local notation "b" => olderGlobalYToInfinity hπ data S 0 h1 m hm
local notation "p" => PrincipalOpenTensor.inclusion S y ≫ (cj).inv
local notation "q" => firstInfinityTensorToInitial hπ data S h1 ≫ (ci).inv

/-- The entire original vertical tensor open is the full first retained infinity intersection. -/
theorem coefficientShearFirstInfinity_isPullback :
    IsPullback b p (atlas (.inl 0)) (atlas (.inr ⟨0, by omega⟩)) := by
  apply (olderGlobalTensor_infinity_isPullback hπ data S 0 h1 m hm).of_iso
    (Iso.refl _) (Iso.refl _) (cj).symm (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, coefficientShearAtlasMap]
    rw [retainedCoefficientShearChart_original hπ data S r 0 h1 m hm]
    simp only [olderGlobalCoefficientShearChart, Nat.add_zero, Iso.inv_hom_id_assoc]

/-- Its entire retained projection factors through the actual initial atlas entry. -/
theorem coefficientShearFirstInfinity_initial :
    q ≫ atlas (.inl 2) = p ≫ atlas (.inr ⟨0, by omega⟩) := by
  change (firstInfinityTensorToInitial hπ data S h1 ≫ (ci).inv) ≫
      (ci).hom ≫ globalInitialTensorChart hπ data S (1 + m) hm =
    (PrincipalOpenTensor.inclusion S y ≫ (cj).inv) ≫
      retainedCoefficientShearChart hπ data S r (1 + m) hm 0 (by omega)
  rw [retainedCoefficientShearChart_original hπ data S r 0 h1 m hm]
  simp only [Category.assoc, olderGlobalCoefficientShearChart, Nat.add_zero,
    Iso.inv_hom_id_assoc]
  exact firstInfinityTensorToInitial_comp hπ data S h1 m hm

/-- The same original boundary also retains its infinity projection through the initial chart. -/
theorem coefficientShearFirstInfinity_initial_infinity :
    q ≫ atlas (.inl 2) = b ≫ atlas (.inl 0) := by
  rw [coefficientShearFirstInfinity_initial]
  exact (coefficientShearFirstInfinity_isPullback hπ data S r m hm).w.symm

/-- Compatible full chart maps agree after any pair of maps with the same ambient composite. -/
theorem fullAtlasPullback_compatible_on {X₁ X₂ X Y Z : Scheme.{u}}
    {a₁ : X₁ ⟶ X} {a₂ : X₂ ⟶ X} {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y}
    (h : pullback.fst a₁ a₂ ≫ f₁ = pullback.snd a₁ a₂ ≫ f₂)
    (p₁ : Z ⟶ X₁) (p₂ : Z ⟶ X₂) (w : p₁ ≫ a₁ = p₂ ≫ a₂) :
    p₁ ≫ f₁ = p₂ ≫ f₂ := by
  have H := congrArg (pullback.lift p₁ p₂ w ≫ ·) h
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using H

/-- The whole first retained infinity cocone equation follows from both initial equations. -/
theorem coefficientShearFirstInfinity_compatible {Y : Scheme.{u}}
    (t : ℕ) (ht : t ≤ n) (ht0 : 1 ≤ t)
    (D : (i : Fin 3 ⊕ Fin t) → coefficientShearAtlasObject data S r t ht i ⟶ Y)
    (hfi : pullback.fst (coefficientShearAtlasMap hπ data S r t ht (.inl 0))
          (coefficientShearAtlasMap hπ data S r t ht (.inl 2)) ≫ D (.inl 0) =
        pullback.snd (coefficientShearAtlasMap hπ data S r t ht (.inl 0))
          (coefficientShearAtlasMap hπ data S r t ht (.inl 2)) ≫ D (.inl 2))
    (hir : pullback.fst (coefficientShearAtlasMap hπ data S r t ht (.inl 2))
          (coefficientShearAtlasMap hπ data S r t ht (.inr ⟨0, ht0⟩)) ≫ D (.inl 2) =
        pullback.snd (coefficientShearAtlasMap hπ data S r t ht (.inl 2))
          (coefficientShearAtlasMap hπ data S r t ht (.inr ⟨0, ht0⟩)) ≫
            D (.inr ⟨0, ht0⟩)) :
    pullback.fst (coefficientShearAtlasMap hπ data S r t ht (.inl 0))
        (coefficientShearAtlasMap hπ data S r t ht (.inr ⟨0, ht0⟩)) ≫ D (.inl 0) =
      pullback.snd (coefficientShearAtlasMap hπ data S r t ht (.inl 0))
        (coefficientShearAtlasMap hπ data S r t ht (.inr ⟨0, ht0⟩)) ≫
          D (.inr ⟨0, ht0⟩) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ht0
  apply fullAtlasPullback_compatible
    (coefficientShearFirstInfinity_isPullback hπ data S r m ht)
  exact (fullAtlasPullback_compatible_on hfi _ _
    (coefficientShearFirstInfinity_initial_infinity hπ data S r m ht).symm).trans
      (fullAtlasPullback_compatible_on hir _ _
        (coefficientShearFirstInfinity_initial hπ data S r m ht))

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearAtlas
public import FLT.Mazur.WeierstrassDividedInitialTensorIntersection

/-!
# The full initial and first retained atlas intersection

Transport the original tensor pullback through the actual coefficient shears.
The entire common principal boundary and both original projections are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (hpos : 1 ≤ t)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, by omega⟩
local notation "x" => WeierstrassDilatation.x W (π ^ start) (d).b3 (d).b4 (d).b6
local notation "t₀" => WeierstrassModificationX.t W (π ^ start) (d).b3 (d).b4 (d).b6
local notation "u₀" => coord W (π ^ start) π (e).b3 (e).b4 (e).b6 2
local notation "A" => PrincipalOpenTensor.transitionIso S x t₀
  (WeierstrassModificationX.overlapEquiv W (π ^ start) (d).b3 (d).b4 (d).b6)
local notation "B" => PrincipalOpenTensor.transitionIso S x u₀ (previousBoundaryEquiv hπ d e)
local notation "ci" => incidenceCoefficientShearIso W (π ^ start)
  (d).b3 (d).b4 (d).b6 S r
local notation "cj" => successiveCoefficientShearIso W (π ^ start) π
  (e).b3 (e).b4 (e).b6 S r
local notation "atlas" => coefficientShearAtlasMap hπ data S r t ht

/-- The original tensor common boundary is the full actual initial/first-retained pullback. -/
theorem coefficientShearInitialAtlas_isPullback :
    IsPullback ((A).inv ≫ PrincipalOpenTensor.inclusion S t₀ ≫ (ci).inv)
      ((B).inv ≫ PrincipalOpenTensor.inclusion S u₀ ≫ (cj).inv)
      (atlas (.inl 2)) (atlas (.inr ⟨0, by omega⟩)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hpos
  apply (initialRetainedGlobalTensor_isPullback hπ data S (by omega) m ht).of_iso
    (Iso.refl _) (ci).symm (cj).symm (Iso.refl _)
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.assoc]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.assoc]
  · change globalInitialTensorChart hπ data S (1 + m) ht ≫ 𝟙 _ =
      (ci).inv ≫ (ci).hom ≫ globalInitialTensorChart hπ data S (1 + m) ht
    simp only [Category.comp_id, Iso.inv_hom_id_assoc]
  · change olderGlobalTensorChart hπ data S 0 (by omega) m ht ≫ 𝟙 _ =
      (cj).inv ≫ retainedCoefficientShearChart hπ data S r (1 + m) ht 0 (by omega)
    rw [retainedCoefficientShearChart_original hπ data S r 0 (by omega) m ht]
    change _ = (cj).inv ≫ (cj).hom ≫ olderGlobalTensorChart hπ data S 0 (by omega) m ht
    simp only [Category.comp_id, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicLocalPointTopology

/-!
# Actual scheme points reconstructed from a complete local adic tower

One common affine neighborhood reconstructs every compatible positive-order
tower. Equality is detected by the same restrictions for arbitrary targets.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.AdicCompleteLocalPoints
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  (I : Ideal R) (hI : I ≠ ⊤) [IsAdicComplete I R] {X : Scheme.{u}}

include hI in
/-- All positive adic restrictions detect scheme points over the original complete local base. -/
theorem hom_ext {f g : Spec (.of R) ⟶ X}
    (h : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫ g) : f = g := by
  have hc : f (closedPoint R) = g (closedPoint R) := by
    rw [← AdicLocalPointTopology.quotient_closed I hI 0]
    exact congrArg (fun k ↦ k (AdicLocalPointTopology.stageClosed I hI 0)) (h 0)
  obtain ⟨U, hU, hfU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := f (closedPoint R)) trivial
  have hgU : g (closedPoint R) ∈ U := hc ▸ hfU
  have hf : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact AdicLocalPointTopology.range_subset f U hfU
  have hg : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact AdicLocalPointTopology.range_subset g U hgU
  let f' := IsOpenImmersion.lift hU.fromSpec f hf
  let g' := IsOpenImmersion.lift hU.fromSpec g hg
  have hff : f' ≫ hU.fromSpec = f := IsOpenImmersion.lift_fac _ _ _
  have hgg : g' ≫ hU.fromSpec = g := IsOpenImmersion.lift_fac _ _ _
  have he : f' = g' := by
    apply AdicCompleteAffinePoints.hom_ext I
    intro m
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, Category.assoc, hff, hgg, h]
  rw [← hff, ← hgg, he]

variable (f : ∀ m : ℕ, Spec (.of (R ⧸ I ^ (m + 1))) ⟶ X)
  (hf : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (S := I ^ (m + 2)) (T := I ^ (m + 1))
    (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))))) ≫ f (m + 1) = f m)

include hI hf in
/-- Compatible scheme maps construct an actual complete-base point with all restrictions. -/
theorem exists_lift : ∃ s : Spec (.of R) ⟶ X, ∀ m : ℕ,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫ s = f m := by
  obtain ⟨U, hU, hrange⟩ := AdicLocalPointTopology.exists_affine I hI f hf
  have hr (m : ℕ) : Set.range (f m) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hrange m
  let g := fun m ↦ IsOpenImmersion.lift hU.fromSpec (f m) (hr m)
  have hg (m : ℕ) : g m ≫ hU.fromSpec = f m := IsOpenImmersion.lift_fac _ _ _
  have hc (m : ℕ) : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))))) ≫ g (m + 1) = g m := by
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, hg, hg, hf]
  refine ⟨AdicCompleteAffinePoints.lift I _ g hc ≫ hU.fromSpec, fun m ↦ ?_⟩
  rw [← Category.assoc, AdicCompleteAffinePoints.quotient_lift, hg]

/-- The reconstructed point over the original ring. -/
def lift : Spec (.of R) ⟶ X := (exists_lift I hI f hf).choose

/-- Each original positive-order map is the actual restriction of the reconstructed point. -/
@[reassoc] theorem quotient_lift (m : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫
      lift I hI f hf = f m := (exists_lift I hI f hf).choose_spec m

/-- The point constructed from a tower is unique, with no separation hypothesis on the target. -/
theorem lift_unique (s : Spec (.of R) ⟶ X)
    (hs : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) ≫
      s = f m) : s = lift I hI f hf := by
  apply hom_ext I hI
  intro m
  rw [hs, quotient_lift]

end FLT.Mazur.AdicCompleteLocalPoints

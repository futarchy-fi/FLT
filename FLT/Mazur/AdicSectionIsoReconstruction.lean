/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicQuotient

/-!
# Transporting adic section reconstruction through actual isomorphisms

An isomorphism of the quotient system carries unique reconstruction to the specified
restriction maps, provided their actual projections and transitions commute.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.IdealAdicQuotient

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (L : X.Modules) [L.IsFinitePresentation]

/-- Unique quotient reconstruction transfers to the original compatible restriction system. -/
theorem existsUnique_section_of_quotient_iso
    (N : ℕ → X.Modules) (e : ∀ m, quotient I L (m + 1) ≅ N m)
    (a : ∀ m, L ⟶ N m) (ha : ∀ m, projection I L (m + 1) ≫ (e m).hom = a m)
    (r : ∀ {i j : ℕ}, i ≤ j → (N j ⟶ N i))
    (he : ∀ i j (hij : i ≤ j), (e j).hom ≫ r hij =
      reduction I L (Nat.add_le_add_right hij 1) ≫ (e i).hom)
    (hrec : ∀ q : ∀ m, Γ(quotient I L (m + 1), ⊤),
      (∀ i j (hij : i ≤ j),
        (reduction I L (Nat.add_le_add_right hij 1)).app ⊤ (q j) = q i) →
      ∃! t : Γ(L, ⊤), ∀ m, (projection I L (m + 1)).app ⊤ t = q m)
    (s : ∀ m, Γ(N m, ⊤)) (hs : ∀ i j (hij : i ≤ j), (r hij).app ⊤ (s j) = s i) :
    ∃! t : Γ(L, ⊤), ∀ m, (a m).app ⊤ t = s m := by
  let q := fun m ↦ (e m).inv.app ⊤ (s m)
  have hq : ∀ i j (hij : i ≤ j),
      (reduction I L (Nat.add_le_add_right hij 1)).app ⊤ (q j) = q i := by
    intro i j hij
    apply (ConcreteCategory.bijective_of_isIso ((e i).hom.app ⊤)).injective
    have ht := congrArg (fun k ↦ k.app ⊤ (q j)) (he i j hij)
    simp only [Hom.comp_app, ConcreteCategory.comp_apply] at ht
    have hq' (m : ℕ) : (e m).hom.app ⊤ (q m) = s m :=
      congrArg (fun k ↦ k.app ⊤ (s m)) (e m).inv_hom_id
    rw [← ht, hq', hq']
    exact hs i j hij
  obtain ⟨t, ht, hu⟩ := hrec q hq
  have iff_image (v : Γ(L, ⊤)) (m : ℕ) :
      (projection I L (m + 1)).app ⊤ v = q m ↔ (a m).app ⊤ v = s m := by
    have hp : (e m).hom.app ⊤ ((projection I L (m + 1)).app ⊤ v) =
        (a m).app ⊤ v := congrArg (fun k ↦ k.app ⊤ v) (ha m)
    rw [← hp]
    constructor
    · intro hv
      rw [hv]
      exact congrArg (fun k ↦ k.app ⊤ (s m)) (e m).inv_hom_id
    · intro hv
      have hv' := congrArg ((e m).inv.app ⊤) hv
      have hv'' := congrArg (fun k ↦ k.app ⊤ ((projection I L (m + 1)).app ⊤ v))
        (e m).hom_inv_id
      exact hv''.symm.trans hv'
  exact ⟨t, fun m ↦ (iff_image t m).mp (ht m),
    fun v hv ↦ hu v (fun m ↦ (iff_image v m).mpr (hv m))⟩

end FLT.Mazur.IdealAdicQuotient

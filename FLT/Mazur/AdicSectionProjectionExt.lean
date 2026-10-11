/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSectionIsoReconstruction

/-!
# Detecting sections by specified adic restriction maps

Unique reconstruction implies joint injectivity of all positive restrictions.
The proof is performed with abstract sheaves, so applications need not unfold
their geometric realization or the underlying sheafification constructions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.IdealAdicQuotient

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (L : X.Modules) [L.IsFinitePresentation]

/-- Reconstruction makes any specified quotient-isomorphic restrictions jointly injective. -/
theorem section_ext_of_quotient_iso
    (N : ℕ → X.Modules) (e : ∀ m, quotient I L (m + 1) ≅ N m)
    (a : ∀ m, L ⟶ N m) (ha : ∀ m, projection I L (m + 1) ≫ (e m).hom = a m)
    (hrec : ∀ q : ∀ m, Γ(quotient I L (m + 1), ⊤),
      (∀ i j (hij : i ≤ j),
        (reduction I L (Nat.add_le_add_right hij 1)).app ⊤ (q j) = q i) →
      ∃! t : Γ(L, ⊤), ∀ m, (projection I L (m + 1)).app ⊤ t = q m)
    (s t : Γ(L, ⊤)) (hst : ∀ m, (a m).app ⊤ s = (a m).app ⊤ t) : s = t := by
  let q := fun m ↦ (projection I L (m + 1)).app ⊤ t
  have hq (i j : ℕ) (hij : i ≤ j) :
      (reduction I L (Nat.add_le_add_right hij 1)).app ⊤ (q j) = q i :=
    congrArg (fun k ↦ k.app ⊤ t) (projection_reduction I L (Nat.add_le_add_right hij 1))
  obtain ⟨v, _, hv⟩ := hrec q hq
  apply (hv s ?_).trans (hv t (fun _ ↦ rfl)).symm
  intro m
  apply (ConcreteCategory.bijective_of_isIso ((e m).hom.app ⊤)).injective
  exact (congrArg (fun k ↦ k.app ⊤ s) (ha m)).trans
    ((hst m).trans (congrArg (fun k ↦ k.app ⊤ t) (ha m)).symm)

end FLT.Mazur.IdealAdicQuotient

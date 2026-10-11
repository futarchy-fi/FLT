/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicOriginalSectionReconstruction

/-!
# Reconstruction through specified original-stage line comparisons

A coherent comparison with original stage modules transports proper formal
section reconstruction. The resulting complete section has the specified
original images, rather than images under newly chosen quotient identifications.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X : Scheme.{u}} (L : X.Modules) (Y : ℕ → Scheme.{u})
  (p : ∀ m, Y m ⟶ X) (r : ∀ {a b : ℕ}, a ≤ b → (Y a ⟶ Y b))
  (hr : ∀ a b (hab : a ≤ b), r hab ≫ p b = p a)

/-- Coherent original stage comparisons transport unique complete section reconstruction. -/
theorem sectionReconstruction_of_stageComparison
    (M : ∀ m, (Y m).Modules)
    (e : ∀ m, (pullback (p m)).obj L ≅ M m)
    (d : ∀ {a b : ℕ}, (hab : a ≤ b) →
      (pullback (r hab)).obj (M b) ⟶ M a)
    (he : ∀ {a b : ℕ} (hab : a ≤ b),
      (pullback (r hab)).map (e b).hom ≫ d hab =
        (pullbackStageIso (p a) (p b) (r hab) (hr a b hab) L).hom ≫ (e a).hom)
    (hrec : ∀ q : ∀ m, Γ((pullback (p m)).obj L, ⊤),
      (∀ a b (hab : a ≤ b),
        (pullbackStageIso (p a) (p b) (r hab) (hr a b hab) L).hom.app ⊤
          (pullGlobal (r hab) _ (q b)) = q a) →
      ∃! t : Γ(L, ⊤), ∀ m, pullGlobal (p m) L t = q m)
    (s : ∀ m, Γ(M m, ⊤))
    (hs : ∀ a b (hab : a ≤ b),
      (d hab).app ⊤
        (pullGlobal (r hab) (M b) (s b)) = s a) :
    ∃! t : Γ(L, ⊤), ∀ m,
      (e m).hom.app ⊤ (pullGlobal (p m) L t) = s m := by
  let q := fun m ↦ (e m).inv.app ⊤ (s m)
  have hq' (m : ℕ) : (e m).hom.app ⊤ (q m) = s m :=
    congrArg (fun k ↦ k.app ⊤ (s m)) (e m).inv_hom_id
  have hq (a b : ℕ) (hab : a ≤ b) :
      (pullbackStageIso (p a) (p b) (r hab) (hr a b hab) L).hom.app ⊤
        (pullGlobal (r hab) _ (q b)) = q a := by
    apply (ConcreteCategory.bijective_of_isIso ((e a).hom.app ⊤)).injective
    have hc := congrArg (fun k ↦ k.app ⊤
      (pullGlobal (r hab) _ (q b))) (he hab)
    simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hc
    rw [← hc, pullGlobal_naturality, hq', hq']
    exact hs a b hab
  obtain ⟨t, ht, hu⟩ := hrec q hq
  refine ⟨t, fun m ↦ (congrArg ((e m).hom.app ⊤) (ht m)).trans (hq' m), ?_⟩
  intro v hv
  apply hu
  intro m
  apply (ConcreteCategory.bijective_of_isIso ((e m).hom.app ⊤)).injective
  exact (hv m).trans (hq' m).symm

end FLT.Mazur.FCurve

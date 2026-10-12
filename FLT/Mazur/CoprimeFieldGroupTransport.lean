/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryCoprimeFieldMarking
public import FLT.Mazur.AuxiliaryLevelGroupTransport

/-!
# Mixed markings commute with an actual group comparison

Prove the complete product-label calculation before specializing group laws
of large geometric constructions. Both field markings and all auxiliary labels
remain visible in the resulting equality of actual parameter morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (G H : CommGrp (Over S)) [IsSeparated G.X.hom]
  [IsSeparated H.X.hom] (e : G ≅ H) (A B : Type) [Group A] [Fintype A]
  [Group B] {K : Type} [Field K] (g : Spec (.of K) ⟶ S)
  (φ : B →* (Over.mk g ⟶ G.X)) (ψ : B →* (Over.mk g ⟶ H.X))
  (he : ∀ b, φ b ≫ e.hom.hom.hom.hom = ψ b)
  {U : Over S} (f : U ⟶ faithfulScheme G.X A) (q : U ⟶ Over.mk g)
include he

/-- Comparing the two field markings suffices to compare all mixed labels. -/
theorem coprimeFieldMarking_groupTransport (c : A × B) :
    coprimeFieldMarking H.X A B g ψ (groupTransportParameter G H e A f) q c =
      coprimeFieldMarking G.X A B g φ f q c ≫ e.hom.hom.hom.hom := by
  rcases c with ⟨a, b⟩
  rw [coprimeFieldMarking_apply, coprimeFieldMarking_apply, MonObj.mul_comp]
  change (groupTransportParameter G H e A f ≫ faithfulInclusion H.X A ≫ value H.X A a) *
    (q ≫ ψ b) = _
  rw [groupTransportParameter_value, Category.assoc, he]

variable [Fintype B] {m n : ℕ} (hm : ∀ a : A, a ^ m = 1)
  (hn : ∀ b : B, b ^ n = 1) (h : m.Coprime n)
  (hφ : Function.Injective φ) (hψ : Function.Injective ψ)

/-- The actual mixed faithful parameter map commutes with the actual group comparison. -/
theorem coprimeFieldLift_groupTransport :
    groupTransportParameter G H e (A × B) (coprimeFieldLift G.X A B g φ hm hn h hφ f q) =
      coprimeFieldLift H.X A B g ψ hm hn h hψ (groupTransportParameter G H e A f) q := by
  apply faithfulParameter_ext H (A × B)
  intro c
  rw [groupTransportParameter_value]
  change (coprimeFieldLift G.X A B g φ hm hn h hφ f q ≫
    faithfulInclusion G.X (A × B) ≫ value G.X (A × B) c) ≫ _ = _
  rw [coprimeFieldLift_value, coprimeFieldLift_value,
    coprimeFieldMarking_groupTransport G H e A B g φ ψ he]

end FLT.Mazur.AuxiliaryLevel

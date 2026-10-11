/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Transporting relation equations through actual open immersions

A commutative square compares regular-function pullbacks using the open
immersions' section isomorphisms. When the relation source has exactly the
required open image, this comparison both preserves and detects invariance.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemeOpenRelationSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {U V P Q : Scheme.{u}} (j : V ⟶ U) (k : Q ⟶ P)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- Pullback in an open square agrees with the original ambient pullback. -/
theorem square_app (a : Q ⟶ V) (p : P ⟶ U) (h : a ≫ j = k ≫ p)
    (W : V.Opens) (D : Q.Opens) (ha : D ≤ a ⁻¹ᵁ W)
    (hp : k ''ᵁ D ≤ p ⁻¹ᵁ (j ''ᵁ W)) :
    (j.appIso W).hom ≫ a.appLE W D ha =
      p.appLE (j ''ᵁ W) (k ''ᵁ D) hp ≫ (k.appIso D).hom := by
  rw [j.appIso_hom', k.appIso_hom', Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 1

/-- The relation-open section isomorphism includes the required domain equality. -/
def relationSectionsIso (a : Q ⟶ V) (p : P ⟶ U) (W : V.Opens)
    (he : k ''ᵁ (a ⁻¹ᵁ W) = p ⁻¹ᵁ (j ''ᵁ W)) :
    Γ(P, p ⁻¹ᵁ (j ''ᵁ W)) ≅ Γ(Q, a ⁻¹ᵁ W) :=
  P.presheaf.mapIso (eqToIso (congrArg op he.symm)) ≪≫ k.appIso _

/-- The first relation endpoint square in the exact original section coordinates. -/
theorem first_square (a : Q ⟶ V) (p : P ⟶ U) (h : a ≫ j = k ≫ p)
    (W : V.Opens) (he : k ''ᵁ (a ⁻¹ᵁ W) = p ⁻¹ᵁ (j ''ᵁ W)) :
    (j.appIso W).hom ≫ a.app W =
      p.app (j ''ᵁ W) ≫ (relationSectionsIso j k a p W he).hom := by
  rw [a.app_eq_appLE]
  exact square_app j k a p h W _ le_rfl he.le

/-- The second endpoint square uses the same actual original relation-open coordinates. -/
theorem second_square (a b : Q ⟶ V) (p q : P ⟶ U) (h : b ≫ j = k ≫ q)
    (W : V.Opens) (he : k ''ᵁ (a ⁻¹ᵁ W) = p ⁻¹ᵁ (j ''ᵁ W))
    (hab : a ⁻¹ᵁ W ≤ b ⁻¹ᵁ W) (hpq : p ⁻¹ᵁ (j ''ᵁ W) ≤ q ⁻¹ᵁ (j ''ᵁ W)) :
    (j.appIso W).hom ≫ b.appLE W (a ⁻¹ᵁ W) hab =
      q.appLE (j ''ᵁ W) (p ⁻¹ᵁ (j ''ᵁ W)) hpq ≫
        (relationSectionsIso j k a p W he).hom := by
  have hh := square_app j k b q h W (a ⁻¹ᵁ W) hab (he.le.trans hpq)
  dsimp only [relationSectionsIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, Scheme.Hom.appLE_map]
  exact hh

/-- Restriction to the actual relation open preserves and detects the invariance equation. -/
theorem compatibility_iff (a b : Q ⟶ V) (p q : P ⟶ U)
    (ha : a ≫ j = k ≫ p) (hb : b ≫ j = k ≫ q)
    (W : V.Opens) (he : k ''ᵁ (a ⁻¹ᵁ W) = p ⁻¹ᵁ (j ''ᵁ W))
    (hab : a ⁻¹ᵁ W ≤ b ⁻¹ᵁ W) (hpq : p ⁻¹ᵁ (j ''ᵁ W) ≤ q ⁻¹ᵁ (j ''ᵁ W))
    (s : Γ(U, j ''ᵁ W)) :
    a.app W ((j.appIso W).hom s) =
        b.appLE W (a ⁻¹ᵁ W) hab ((j.appIso W).hom s) ↔
      p.app (j ''ᵁ W) s = q.appLE (j ''ᵁ W) (p ⁻¹ᵁ (j ''ᵁ W)) hpq s := by
  have h₁ := congrArg (fun m ↦ m s) (first_square j k a p ha W he)
  have h₂ := congrArg (fun m ↦ m s) (second_square j k a b p q hb W he hab hpq)
  simp only [ConcreteCategory.comp_apply] at h₁ h₂
  rw [h₁, h₂]
  exact (relationSectionsIso j k a p W he).commRingCatIsoToRingEquiv.injective.eq_iff

end FLT.Mazur.SchemeOpenRelationSections

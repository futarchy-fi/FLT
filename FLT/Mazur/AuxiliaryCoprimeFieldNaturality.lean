/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryCoprimeFieldMarking

/-!
# Naturality and factor restrictions of the actual combined marking map

The morphism to the faithful marking open commutes with all test-scheme maps.
Restriction to either factor recovers the specified auxiliary or field section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [CommGrpObj E] [IsSeparated E.hom]
  (A B : Type) [Group A] [Fintype A] [Group B] [Fintype B]
  {K : Type} [Field K] (g : Spec (.of K) ⟶ S) (φ : B →* (Over.mk g ⟶ E))
  {m n : ℕ} (hm : ∀ a : A, a ^ m = 1) (hn : ∀ b : B, b ^ n = 1)
  (h : m.Coprime n) (hφ : Function.Injective φ)
  {U : Over S} (f : U ⟶ faithfulScheme E A) (q : U ⟶ Over.mk g)

/-- The constructed map of faithful marking schemes retains every further test map. -/
@[reassoc] theorem coprimeFieldLift_natural {V : Over S} (k : V ⟶ U) :
    k ≫ coprimeFieldLift E A B g φ hm hn h hφ f q =
      coprimeFieldLift E A B g φ hm hn h hφ (k ≫ f) (k ≫ q) := by
  have he : (k ≫ coprimeFieldLift E A B g φ hm hn h hφ f q) ≫
      faithfulInclusion E (A × B) =
        coprimeFieldLift E A B g φ hm hn h hφ (k ≫ f) (k ≫ q) ≫
          faithfulInclusion E (A × B) := by
    apply homScheme_ext
    intro c
    simp only [Category.assoc, coprimeFieldLift_value, coprimeFieldMarking_natural]
  apply Over.OverMorphism.ext
  apply (cancel_mono (faithfulOpen E (A × B)).ι).mp
  exact congrArg Over.Hom.left he

/-- Restricting the actual combined map to the auxiliary factor recovers its original value. -/
@[reassoc] theorem coprimeFieldLift_auxiliary (a : A) :
    coprimeFieldLift E A B g φ hm hn h hφ f q ≫ faithfulInclusion E (A × B) ≫
      value E (A × B) (a, 1) = markingOf E A (f ≫ faithfulInclusion E A) a := by
  rw [coprimeFieldLift_value, coprimeFieldMarking_apply, map_one, comp_one, _root_.mul_one]

/-- Restricting the actual combined map to the field factor recovers its original value. -/
@[reassoc] theorem coprimeFieldLift_field (b : B) :
    coprimeFieldLift E A B g φ hm hn h hφ f q ≫ faithfulInclusion E (A × B) ≫
      value E (A × B) (1, b) = q ≫ φ b := by
  rw [coprimeFieldLift_value, coprimeFieldMarking_apply, map_one, _root_.one_mul]

end FLT.Mazur.AuxiliaryLevel

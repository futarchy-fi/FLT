/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterCommonCoefficientGroup
public import FLT.Mazur.CharacterCoefficientHomDetection

/-!
# Original recovery detects independent character-model comparisons

After putting two initial coefficient rings in a common ring, equality can
be checked over any injective extension of that ring. This compares entire
scheme morphisms to separated targets, without a flatness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CharacterSchemeBaseChange
universe u
variable (A B C R G : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing R]
  [Algebra A C] [Algebra B C] [Algebra C R] [AddCommMonoid G]
  (hinj : Function.Injective (algebraMap C R))
  {Y Z : Over (Spec (.of C))} [IsSeparated Z.hom]
  (e : Y ≅ Z)
  (f : (Over.pullback (baseMap A C)).obj (model A G) ⟶ Y)
  (g : (Over.pullback (baseMap B C)).obj (model B G) ⟶ Z)

include hinj in
/-- Injective recovery detects the square between independent whole character sources. -/
theorem commonGroupIso_square_of_recovery
    (h : (Over.pullback (baseMap C R)).map ((overIso A C G).hom ≫ f ≫ e.hom) =
      (Over.pullback (baseMap C R)).map ((overIso B C G).hom ≫ g)) :
    f ≫ e.hom = (commonGroupIso A B C G).hom ≫ g := by
  apply (cancel_epi (overIso A C G).hom).mp
  rw [commonGroupIso_recovery_assoc]
  exact pullback_map_injective C R G hinj Z h

include hinj in
/-- Recovery may be given on the actual character scheme over the original ring. -/
theorem commonGroupIso_square_of_actual_recovery
    (h : (overIso C R G).hom ≫
        (Over.pullback (baseMap C R)).map ((overIso A C G).hom ≫ f ≫ e.hom) =
      (overIso C R G).hom ≫
        (Over.pullback (baseMap C R)).map ((overIso B C G).hom ≫ g)) :
    f ≫ e.hom = (commonGroupIso A B C G).hom ≫ g := by
  apply commonGroupIso_square_of_recovery A B C R G hinj e f g
  exact (cancel_epi (overIso C R G).hom).mp h

omit [IsSeparated Z.hom] in
/-- Any further base change retains the comparison, including the full source morphism. -/
theorem commonGroupIso_square_baseChange (h : f ≫ e.hom =
    (commonGroupIso A B C G).hom ≫ g) {T : Scheme.{u}} (v : T ⟶ Spec (.of C)) :
    (Over.pullback v).map f ≫ (Over.pullback v).map e.hom =
      (Over.pullback v).map (commonGroupIso A B C G).hom ≫ (Over.pullback v).map g := by
  simpa only [Functor.map_comp] using congrArg (fun k => (Over.pullback v).map k) h

end FLT.Mazur.CharacterSchemeBaseChange

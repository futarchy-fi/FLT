/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterSchemeMapComparison

/-!
# Character maps along coefficient towers

Direct and iterated coefficient extension agree on the entire intrinsic
character map into any relative scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A B C M : Type) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [AddCommMonoid M]

/-- A tower comparison preserving the original projection transports the full character map. -/
theorem intrinsicMap_comparison (X : Over (Spec (.of A))) (f : model A M ⟶ X)
    (d : (Over.pullback (baseMap A C)).obj X ⟶
      (Over.pullback (baseMap B C)).obj ((Over.pullback (baseMap A B)).obj X))
    (hd : d.left ≫ Limits.pullback.fst (Limits.pullback.snd X.hom (baseMap A B))
        (baseMap B C) ≫ Limits.pullback.fst X.hom (baseMap A B) =
      Limits.pullback.fst X.hom (baseMap A C)) :
    ((overIso A C M).hom ≫ (Over.pullback (baseMap A C)).map f) ≫ d =
    (overIso B C M).hom ≫ (Over.pullback (baseMap B C)).map
      ((overIso A B M).hom ≫ (Over.pullback (baseMap A B)).map f) := by
  rw [← sourceIso_def, ← sourceIso_def, ← sourceIso_def]
  exact sourceMap_comparison A B C M X f d hd

end FLT.Mazur.CharacterSchemeBaseChange

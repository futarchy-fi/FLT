/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import FLT.Mazur.CoprimeGroupMarkings

/-!
# Complete coprime markings over arbitrary bases

Auxiliary and cyclic markings combine faithfully on every test scheme when
the label exponents are coprime. No field or reducedness assumption is used.
The resulting actual parameter retains both original factors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [CommGrpObj E] [IsSeparated E.hom]
  (A B : Type) [Group A] [Fintype A] [Group B] [Fintype B]

/-- Combine the two original complete markings by the existing commutative group law. -/
def coprimeMarking {U : Over S} (f : U ⟶ faithfulScheme E A)
    (g : U ⟶ faithfulScheme E B) : A × B →* (U ⟶ E) :=
  (markingOf E A (f ≫ faithfulInclusion E A)).coprod
    (markingOf E B (g ≫ faithfulInclusion E B))

/-- Each product label retains the actual two original sections. -/
theorem coprimeMarking_apply {U : Over S} (f : U ⟶ faithfulScheme E A)
    (g : U ⟶ faithfulScheme E B) (a : A) (b : B) :
    coprimeMarking E A B f g (a, b) =
      markingOf E A (f ≫ faithfulInclusion E A) a *
        markingOf E B (g ≫ faithfulInclusion E B) b := rfl

/-- The complete product marking commutes with arbitrary test maps. -/
theorem coprimeMarking_natural {U V : Over S} (f : U ⟶ faithfulScheme E A)
    (g : U ⟶ faithfulScheme E B) (k : V ⟶ U) (c : A × B) :
    coprimeMarking E A B (k ≫ f) (k ≫ g) c = k ≫ coprimeMarking E A B f g c := by
  rcases c with ⟨a, b⟩
  simp only [coprimeMarking_apply, Category.assoc, markingOf_comp, comp_mul]

variable {m n : ℕ} (hm : ∀ a : A, a ^ m = 1) (hn : ∀ b : B, b ^ n = 1)
  (h : m.Coprime n)
include hm hn h

/-- Coprimality rules out collisions of mixed labels on every nonempty test. -/
theorem coprimeMarking_injective {U : Over S} (f : U ⟶ faithfulScheme E A)
    (g : U ⟶ faithfulScheme E B) [Nonempty U.left] :
    Function.Injective (coprimeMarking E A B f g) :=
  CoprimeGroupMarkings.coprod_injective _ _ hm hn h
    (faithful_marking_injective E A f) (faithful_marking_injective E B g)

/-- Universal faithfulness holds for the entire combined marking. -/
theorem coprimeMarking_faithful {U : Over S} (f : U ⟶ faithfulScheme E A)
    (g : U ⟶ faithfulScheme E B) :
    UniversallyFaithful E (A × B) (liftMarking E (A × B) (coprimeMarking E A B f g)) := by
  intro V k hV
  let _ := hV
  intro a b hab
  apply coprimeMarking_injective E A B hm hn h (k ≫ f) (k ≫ g)
  rw [coprimeMarking_natural, coprimeMarking_natural]
  change (k ≫ liftMarking E (A × B) _) ≫ value E (A × B) a =
    (k ≫ liftMarking E (A × B) _) ≫ value E (A × B) b at hab
  simpa only [Category.assoc, liftMarking_value] using hab

/-- The complete product labeling gives an actual point of the faithful marking open. -/
def coprimeParameter {U : Over S} (f : U ⟶ faithfulScheme E A)
    (g : U ⟶ faithfulScheme E B) : U ⟶ faithfulScheme E (A × B) :=
  faithfulLift E (A × B) (liftMarking E (A × B) (coprimeMarking E A B f g))
    (coprimeMarking_faithful E A B hm hn h f g)

/-- The resulting parameter preserves every original product section. -/
@[reassoc] theorem coprimeParameter_value {U : Over S} (f : U ⟶ faithfulScheme E A)
    (g : U ⟶ faithfulScheme E B) (c : A × B) :
    coprimeParameter E A B hm hn h f g ≫ faithfulInclusion E (A × B) ≫
      value E (A × B) c = coprimeMarking E A B f g c := by
  rw [← Category.assoc, coprimeParameter, faithfulLift_inclusion, liftMarking_value]

end FLT.Mazur.AuxiliaryLevel

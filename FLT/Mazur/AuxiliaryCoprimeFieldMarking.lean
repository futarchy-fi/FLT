/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFieldMarking
public import FLT.Mazur.CoprimeGroupMarkings

/-!
# Auxiliary markings combined with a retained field marking

An auxiliary marking and a faithful field marking of coprime exponent combine
on every test scheme into an actual point of the faithful product-label scheme.
The construction retains the field map and every section under further pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [CommGrpObj E] [IsSeparated E.hom]
  (A B : Type) [Group A] [Fintype A] [Group B] [Fintype B]
  {K : Type} [Field K] (g : Spec (.of K) ⟶ S)
  (φ : B →* (Over.mk g ⟶ E))

/-- Pull the retained field marking back along the specified map of test schemes. -/
def fieldMarkingOn {U : Over S} (q : U ⟶ Over.mk g) : B →* (U ⟶ E) :=
  ((yonedaGrpObj E).map q.op).hom.comp φ

omit [IsSeparated E.hom] [Fintype B] in
/-- A faithful field marking remains faithful on every nonempty test scheme. -/
theorem fieldMarkingOn_injective [Finite B] (hφ : Function.Injective φ)
    {U : Over S} (q : U ⟶ Over.mk g) [Nonempty U.left] :
    Function.Injective (fieldMarkingOn E B g φ q) := by
  let _ := Fintype.ofFinite B
  have h := fieldMarking_universallyFaithful E B g φ hφ U q inferInstance
  intro a b hab
  apply h
  change q ≫ φ a = q ≫ φ b at hab
  change (q ≫ liftMarking E B φ) ≫ value E B a =
    (q ≫ liftMarking E B φ) ≫ value E B b
  simpa only [Category.assoc, liftMarking_value] using hab

/-- Combine all auxiliary labels with the original field labels. -/
def coprimeFieldMarking {U : Over S} (f : U ⟶ faithfulScheme E A)
    (q : U ⟶ Over.mk g) : A × B →* (U ⟶ E) :=
  (markingOf E A (f ≫ faithfulInclusion E A)).coprod (fieldMarkingOn E B g φ q)

omit [Fintype B] in
/-- Every product label keeps its two specified constituent sections. -/
theorem coprimeFieldMarking_apply {U : Over S} (f : U ⟶ faithfulScheme E A)
    (q : U ⟶ Over.mk g) (a : A) (b : B) :
    coprimeFieldMarking E A B g φ f q (a, b) =
      markingOf E A (f ≫ faithfulInclusion E A) a * (q ≫ φ b) := rfl

omit [Fintype B] in
/-- The complete combined marking commutes with every change of test scheme. -/
theorem coprimeFieldMarking_natural {U V : Over S} (f : U ⟶ faithfulScheme E A)
    (q : U ⟶ Over.mk g) (k : V ⟶ U) (c : A × B) :
    coprimeFieldMarking E A B g φ (k ≫ f) (k ≫ q) c =
      k ≫ coprimeFieldMarking E A B g φ f q c := by
  rcases c with ⟨a, b⟩
  simp only [coprimeFieldMarking_apply, Category.assoc, markingOf_comp, comp_mul]

variable {m n : ℕ} (hm : ∀ a : A, a ^ m = 1) (hn : ∀ b : B, b ^ n = 1)
  (h : m.Coprime n) (hφ : Function.Injective φ)
include hm hn h hφ

omit [Fintype B] in
/-- Coprimality proves that no mixed label vanishes on a nonempty test. -/
theorem coprimeFieldMarking_injective [Finite B] {U : Over S} (f : U ⟶ faithfulScheme E A)
    (q : U ⟶ Over.mk g) [Nonempty U.left] :
    Function.Injective (coprimeFieldMarking E A B g φ f q) :=
  CoprimeGroupMarkings.coprod_injective _ _ hm hn h
    (faithful_marking_injective E A f) (fieldMarkingOn_injective E B g φ hφ q)

/-- The original combined equation point is universally faithful. -/
theorem coprimeFieldMarking_faithful {U : Over S} (f : U ⟶ faithfulScheme E A)
    (q : U ⟶ Over.mk g) :
    UniversallyFaithful E (A × B) (liftMarking E (A × B)
      (coprimeFieldMarking E A B g φ f q)) := by
  intro V k hV
  let _ := hV
  intro a b hab
  apply coprimeFieldMarking_injective E A B g φ hm hn h hφ (k ≫ f) (k ≫ q)
  rw [coprimeFieldMarking_natural, coprimeFieldMarking_natural]
  change (k ≫ liftMarking E (A × B) _) ≫ value E (A × B) a =
    (k ≫ liftMarking E (A × B) _) ≫ value E (A × B) b at hab
  simpa only [Category.assoc, liftMarking_value] using hab

/-- The combined labels define an actual morphism to the faithful marking open. -/
def coprimeFieldLift {U : Over S} (f : U ⟶ faithfulScheme E A)
    (q : U ⟶ Over.mk g) : U ⟶ faithfulScheme E (A × B) :=
  faithfulLift E (A × B) (liftMarking E (A × B) (coprimeFieldMarking E A B g φ f q))
    (coprimeFieldMarking_faithful E A B g φ hm hn h hφ f q)

/-- The actual morphism retains each original combined section. -/
@[reassoc] theorem coprimeFieldLift_value {U : Over S} (f : U ⟶ faithfulScheme E A)
    (q : U ⟶ Over.mk g) (c : A × B) :
    coprimeFieldLift E A B g φ hm hn h hφ f q ≫ faithfulInclusion E (A × B) ≫
      value E (A × B) c = coprimeFieldMarking E A B g φ f q c := by
  rw [← Category.assoc, coprimeFieldLift, faithfulLift_inclusion, liftMarking_value]

end FLT.Mazur.AuxiliaryLevel

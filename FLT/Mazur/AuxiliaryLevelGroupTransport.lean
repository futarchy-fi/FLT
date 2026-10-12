/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import FLT.Mazur.GroupMarkingTransport

/-!
# Faithful marking schemes retain actual group isomorphisms

Postcomposition with a group-scheme isomorphism gives an actual isomorphism
of faithful marking schemes. Every label and test-scheme map is retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (G H : CommGrp (Over S)) [IsSeparated G.X.hom]
  [IsSeparated H.X.hom] (e : G ≅ H) (A : Type) [Group A] [Fintype A]

/-- An actual group comparison transports the full marking on every original test. -/
def groupTransportMarking {U : Over S} (f : U ⟶ faithfulScheme G.X A) : A →* (U ⟶ H.X) :=
  GroupMarkingTransport.transport G H e (markingOf G.X A (f ≫ faithfulInclusion G.X A))

omit [IsSeparated H.X.hom] in
/-- Every transported equation point is universally faithful. -/
theorem groupTransportMarking_faithful {U : Over S} (f : U ⟶ faithfulScheme G.X A) :
    UniversallyFaithful H.X A (liftMarking H.X A (groupTransportMarking G H e A f)) := by
  intro V k hV
  let _ := hV
  intro a b hab
  have hi := (GroupMarkingTransport.transport_injective_iff G H e
    (markingOf G.X A ((k ≫ f) ≫ faithfulInclusion G.X A))).mpr
      (faithful_marking_injective G.X A (k ≫ f))
  apply hi
  change (k ≫ liftMarking H.X A _) ≫ value H.X A a =
    (k ≫ liftMarking H.X A _) ≫ value H.X A b at hab
  simp only [Category.assoc, liftMarking_value] at hab
  change k ≫ (markingOf G.X A (f ≫ faithfulInclusion G.X A) a ≫ e.hom.hom.hom.hom) =
    k ≫ (markingOf G.X A (f ≫ faithfulInclusion G.X A) b ≫ e.hom.hom.hom.hom) at hab
  change markingOf G.X A ((k ≫ f) ≫ faithfulInclusion G.X A) a ≫ e.hom.hom.hom.hom =
    markingOf G.X A ((k ≫ f) ≫ faithfulInclusion G.X A) b ≫ e.hom.hom.hom.hom
  simpa only [Category.assoc, markingOf_comp] using hab

/-- The transported marking determines a morphism to the actual faithful open. -/
def groupTransportParameter {U : Over S} (f : U ⟶ faithfulScheme G.X A) :
    U ⟶ faithfulScheme H.X A :=
  faithfulLift H.X A (liftMarking H.X A (groupTransportMarking G H e A f))
    (groupTransportMarking_faithful G H e A f)

/-- The constructed parameter map retains exactly the original group comparison on each label. -/
@[reassoc] theorem groupTransportParameter_value {U : Over S}
    (f : U ⟶ faithfulScheme G.X A) (a : A) :
    groupTransportParameter G H e A f ≫ faithfulInclusion H.X A ≫ value H.X A a =
      markingOf G.X A (f ≫ faithfulInclusion G.X A) a ≫ e.hom.hom.hom.hom := by
  rw [← Category.assoc, groupTransportParameter, faithfulLift_inclusion, liftMarking_value]
  rfl

/-- Equality of every marked section detects equality of faithful parameter maps. -/
theorem faithfulParameter_ext {U : Over S} (f g : U ⟶ faithfulScheme G.X A)
    (he : ∀ a, f ≫ faithfulInclusion G.X A ≫ value G.X A a =
      g ≫ faithfulInclusion G.X A ≫ value G.X A a) : f = g := by
  have hi : f ≫ faithfulInclusion G.X A = g ≫ faithfulInclusion G.X A := by
    apply homScheme_ext
    intro a
    exact (Category.assoc _ _ _).trans ((he a).trans (Category.assoc _ _ _).symm)
  apply Over.OverMorphism.ext
  apply (cancel_mono (faithfulOpen G.X A).ι).mp
  exact congrArg Over.Hom.left hi

/-- Transport commutes with every change of test scheme. -/
@[reassoc] theorem groupTransportParameter_natural {U V : Over S}
    (f : U ⟶ faithfulScheme G.X A) (k : V ⟶ U) :
    k ≫ groupTransportParameter G H e A f = groupTransportParameter G H e A (k ≫ f) := by
  apply faithfulParameter_ext H A
  intro a
  simp only [Category.assoc, groupTransportParameter_value, markingOf_comp]

/-- The inverse group comparison restores the original parameter map. -/
theorem groupTransportParameter_inverse {U : Over S} (f : U ⟶ faithfulScheme G.X A) :
    groupTransportParameter H G e.symm A (groupTransportParameter G H e A f) = f := by
  apply faithfulParameter_ext G A
  intro a
  rw [groupTransportParameter_value]
  change (groupTransportParameter G H e A f ≫ faithfulInclusion H.X A ≫ value H.X A a) ≫
    e.inv.hom.hom.hom = _
  rw [groupTransportParameter_value, Category.assoc]
  have he : e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom = 𝟙 _ :=
    congrArg (fun k ↦ k.hom.hom.hom) e.hom_inv_id
  rw [he, Category.comp_id]
  rfl

/-- An actual group isomorphism induces an isomorphism of the faithful marking schemes. -/
def groupTransportIso : faithfulScheme G.X A ≅ faithfulScheme H.X A where
  hom := groupTransportParameter G H e A (𝟙 _)
  inv := groupTransportParameter H G e.symm A (𝟙 _)
  hom_inv_id := by
    rw [groupTransportParameter_natural, Category.comp_id, groupTransportParameter_inverse]
  inv_hom_id := by
    rw [groupTransportParameter_natural, Category.comp_id]
    exact groupTransportParameter_inverse H G e.symm A (𝟙 _)

end FLT.Mazur.AuxiliaryLevel

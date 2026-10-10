/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelKernelLocus
public import FLT.Mazur.FiniteGroupOpenRestriction

/-!
# The open scheme of faithful auxiliary markings

Remove the finitely many closed loci where a nonidentity label becomes the
identity. The actual relabeling action preserves this open scheme. Every
nonempty test scheme mapping into it has an injective marking homomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.AuxiliaryLevel

variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (A : Type) [Group A] [Fintype A]

/-- The complement of every nontrivial kernel equation. -/
def faithfulOpen : (homScheme E A).left.Opens :=
  ⟨⋂ a : {a : A // a ≠ 1}, (kernelLocus E a.val)ᶜ,
    isOpen_iInter_of_finite fun a => (kernelLocus_isClosed E a.val).isOpen_compl⟩

/-- Membership tests the actual scheme equalizer loci. -/
theorem mem_faithfulOpen (x : (homScheme E A).left) :
    x ∈ faithfulOpen E A ↔ ∀ a : A, a ≠ 1 → x ∉ kernelLocus E a := by
  simp only [faithfulOpen, TopologicalSpace.Opens.mem_mk, Set.mem_iInter,
    Set.mem_compl_iff, Subtype.forall]

/-- The faithful-marking open is stable under the constructed finite-group action. -/
theorem faithfulOpen_stable (e : MulAut A) :
    (relabelSchemeAction E e).hom ⁻¹ᵁ faithfulOpen E A = faithfulOpen E A := by
  ext x
  change (relabelSchemeAction E e).hom x ∈ faithfulOpen E A ↔ x ∈ faithfulOpen E A
  rw [mem_faithfulOpen, mem_faithfulOpen]
  have h (a : A) : (relabelSchemeAction E e).hom x ∈ kernelLocus E a ↔
      x ∈ kernelLocus E (e.symm a) :=
    Set.ext_iff.mp (relabel_preimage_kernelLocus E e a) x
  constructor
  · intro hx a ha
    have he : e a ≠ 1 := fun he => ha (e.injective (he.trans (e.map_one).symm))
    simpa only [e.symm_apply_apply] using (h (e a)).not.mp (hx (e a) he)
  · intro hx a ha
    have he : e.symm a ≠ 1 :=
      fun he => ha (e.symm.injective (he.trans (e.symm.map_one).symm))
    exact (h a).not.mpr (hx (e.symm a) he)

/-- The constructed faithful-marking scheme with its original base morphism. -/
def faithfulScheme : Over S := Over.mk ((faithfulOpen E A).ι ≫ (homScheme E A).hom)

/-- The actual open immersion in the marking equation scheme. -/
def faithfulInclusion : faithfulScheme E A ⟶ homScheme E A :=
  Over.homMk (faithfulOpen E A).ι rfl

/-- The finite-group action on the faithful-marking scheme. -/
def faithfulAction : MulAut A →* Aut (faithfulScheme E A).left :=
  FiniteGroupRestriction.restrictedAction (relabelSchemeAction E)
    (faithfulOpen E A) (faithfulOpen_stable E A)

/-- The open immersion is equivariant for the actual two actions. -/
@[reassoc] theorem faithfulAction_inclusion (e : MulAut A) :
    (faithfulAction E A e).hom ≫ (faithfulInclusion E A).left =
      (faithfulInclusion E A).left ≫ (relabelSchemeAction E e).hom :=
  FiniteGroupRestriction.restrictedAction_hom_ι _ _ _ e

/-- The action preserves the scheme morphism to the base. -/
@[reassoc] theorem faithfulAction_base (e : MulAut A) :
    (faithfulAction E A e).hom ≫ (faithfulScheme E A).hom =
      (faithfulScheme E A).hom := by
  change _ ≫ (faithfulInclusion E A).left ≫ (homScheme E A).hom = _
  rw [← Category.assoc, faithfulAction_inclusion, Category.assoc,
    relabelSchemeAction_base]
  rfl

/-- A nontrivial label cannot vanish on a nonempty test scheme in the faithful open. -/
theorem faithful_marking_ne_one {U : Over S} (f : U ⟶ faithfulScheme E A)
    (x : U.left) (a : A) (ha : a ≠ 1) :
    markingOf E A (f ≫ faithfulInclusion E A) a ≠ 1 := by
  intro h
  let g := f ≫ faithfulInclusion E A
  have he : g ≫ value E A a = g ≫ 1 := by
    change g ≫ value E A a = 1 at h
    rw [h, MonObj.comp_one]
  let k : U ⟶ kernelScheme E a := equalizer.lift g he
  have hk : (kernelInclusion E a).left (k.left x) = g.left x :=
    congrArg (fun m : U ⟶ homScheme E A => m.left x) (equalizer.lift_ι g he)
  have hx : g.left x ∈ faithfulOpen E A := (f.left x).property
  exact (mem_faithfulOpen E A _).mp hx a ha ⟨k.left x, hk⟩

/-- The represented marking is injective on sections of every nonempty test scheme. -/
theorem faithful_marking_injective {U : Over S} (f : U ⟶ faithfulScheme E A)
    [Nonempty U.left] : Function.Injective (markingOf E A (f ≫ faithfulInclusion E A)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  by_contra h
  exact faithful_marking_ne_one E A f (Classical.choice ‹Nonempty U.left›) a h ha

end FLT.Mazur.AuxiliaryLevel

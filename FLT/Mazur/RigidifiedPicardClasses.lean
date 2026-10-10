/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedLineIsomorphismExistence
public import FLT.Mazur.PointedPicardNormalization

/-!
# Rigidified line bundles and the Picard kernel

These objects carry an actual trivialization at the section. Their equivalence
relation uses isomorphisms preserving those trivializations. The resulting
classes are equivalent to the Picard kernel, by the scalar correction theorem.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{u}} (s : S ⟶ X)

/-- A line bundle together with an actual chosen trivialization on the section. -/
def RigidifiedBundle :=
  Σ L : LineBundle X, (Scheme.Modules.pullback s).obj L.val ≅ structureModule S

/-- Isomorphisms of rigidified bundles must preserve the specified trivializations. -/
def rigidifiedBundleSetoid : Setoid (RigidifiedBundle s) where
  r L M := Nonempty (RigidifiedIso s L.2 M.2)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro L
      exact ⟨⟨Iso.refl L.1.val, by simp⟩⟩
    · intro L M h
      obtain ⟨i, hi⟩ := h
      refine ⟨⟨i.symm, ?_⟩⟩
      simp only [Iso.symm_hom]
      apply (cancel_epi ((Scheme.Modules.pullback s).map i.hom)).mp
      rw [← Category.assoc, ← Functor.map_comp, i.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, hi]
    · intro L M N h k
      obtain ⟨i, hi⟩ := h
      obtain ⟨j, hj⟩ := k
      refine ⟨⟨i ≪≫ j, ?_⟩⟩
      simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, hj, hi]

/-- Isomorphism classes of actual rigidified line bundles. -/
def RigidifiedPic := Quotient (rigidifiedBundleSetoid s)

/-- The kernel element represented by an actual rigidified line bundle. -/
def rigidifiedBundleKernel (L : RigidifiedBundle s) : (pullback s).ker :=
  ⟨mk L.1.val L.1.property, (mk_eq_one_iff _ _).mpr ⟨L.2⟩⟩

/-- Forgetting a rigidification descends to its Picard kernel class. -/
def rigidifiedKernel : RigidifiedPic s → (pullback s).ker :=
  Quotient.lift (rigidifiedBundleKernel s) (by
    intro L M h
    obtain ⟨i⟩ := h
    exact Subtype.ext (mk_eq_of_iso L.1.property M.1.property i.val))

/-- Kernel classes have representatives with an actual chosen rigidification. -/
theorem rigidifiedBundleKernel_surjective : Function.Surjective (rigidifiedBundleKernel s) := by
  intro a
  obtain ⟨M, hM, h⟩ : ∃ (M : X.Modules) (hM : LocallyFreeRankOne M), mk M hM = a.val :=
    inductionOn a.val (fun M hM ↦ ⟨M, hM, rfl⟩)
  have hm : pullback s (mk M hM) = 1 := h ▸ a.property
  obtain ⟨ρ⟩ := (mk_eq_one_iff _ _).mp hm
  exact ⟨⟨⟨M, hM⟩, ρ⟩, Subtype.ext h⟩

/-- Every kernel element is represented by a rigidified isomorphism class. -/
theorem rigidifiedKernel_surjective : Function.Surjective (rigidifiedKernel s) := by
  intro a
  obtain ⟨L, hL⟩ := rigidifiedBundleKernel_surjective s a
  exact ⟨Quotient.mk _ L, hL⟩

variable (f : X ⟶ S) (hs : s ≫ f = 𝟙 S)

include hs in
/-- Scalar correction identifies any two rigidified representatives of a kernel class. -/
theorem rigidifiedKernel_injective : Function.Injective (rigidifiedKernel s) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro L M h
  apply Quotient.sound
  apply (rigidifiedIso_nonempty_iff f s hs L.1.property L.2 M.2).mpr
  apply (mk_eq_mk_iff L.1.property M.1.property).mp
  exact congrArg Subtype.val h

/-- Actual rigidified line-bundle classes are exactly the Picard restriction kernel. -/
def rigidifiedKernelEquiv : RigidifiedPic s ≃ (pullback s).ker :=
  Equiv.ofBijective (rigidifiedKernel s)
    ⟨rigidifiedKernel_injective s f hs, rigidifiedKernel_surjective s⟩

/-- The equivalence retains the underlying class of the given actual line bundle. -/
theorem rigidifiedKernelEquiv_mk (L : RigidifiedBundle s) :
    (rigidifiedKernelEquiv s f hs (Quotient.mk _ L)).val = mk L.1.val L.1.property := rfl

end FLT.Mazur.SchemePicard

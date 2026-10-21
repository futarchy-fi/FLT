/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenCoefficientGluing

/-!
# Extension by zero across a clopen decomposition

A section on one component extends uniquely with value zero on its open
complement. The construction works on nonaffine schemes with nilpotents.
Its uniqueness will supply compatibility under every order transition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeClopenSectionExtension
open InvariantOpenCoefficientGluing
variable {X : Scheme.{0}} (U V : X.Opens)

/-- A disjoint intersection has only one section, including on its full scheme structure. -/
theorem section_eq_of_disjoint (h : U ⊓ V = ⊥)
    (s t : Γ((U ⊓ V).toScheme, ⊤)) : s = t := by
  have : Subsingleton Γ(X, U ⊓ V) := by rw [h]; infer_instance
  exact (U ⊓ V).topIso.commRingCatIsoToRingEquiv.injective (Subsingleton.elim _ _)

/-- Two opens covering the source detect equality of global sections. -/
theorem section_ext_pair (h : U ⊔ V = ⊤) (s t : Γ(X, ⊤))
    (hU : U.ι.appTop s = U.ι.appTop t) (hV : V.ι.appTop s = V.ι.appTop t) : s = t := by
  apply section_ext (fun b : Bool ↦ if b then U else V) (by
    simp only [iSup_bool_eq, Bool.false_eq_true, ite_false, ite_true]
    exact h) s t
  intro b
  cases b
  · exact hV
  · exact hU

/-- Arbitrary sections on disjoint complementary opens glue without a compatibility condition. -/
theorem existsUnique_pair (hdis : U ⊓ V = ⊥) (hcover : U ⊔ V = ⊤)
    (s : Γ(U.toScheme, ⊤)) (t : Γ(V.toScheme, ⊤)) :
    ∃! z : Γ(X, ⊤), U.ι.appTop z = s ∧ V.ι.appTop z = t := by
  let W : Bool → X.Opens := fun b ↦ if b then U else V
  let v : ∀ b, Γ((W b).toScheme, ⊤) := fun b ↦ by
    cases b
    · exact t
    · exact s
  have hc : iSup W = ⊤ := by
    simp only [W, iSup_bool_eq, Bool.false_eq_true, ite_false, ite_true]
    exact hcover
  obtain ⟨z, hz, _⟩ := existsUnique_section W hc v (by
    intro i j
    cases i <;> cases j
    · rfl
    · exact section_eq_of_disjoint V U (by simpa [inf_comm] using hdis) _ _
    · exact section_eq_of_disjoint U V hdis _ _
    · rfl)
  exact ⟨z, ⟨hz true, hz false⟩, fun w hw ↦
    section_ext_pair U V hcover w z (hw.1.trans (hz true).symm)
      (hw.2.trans (hz false).symm)⟩

/-- The unique global section with the prescribed value and zero on the complement. -/
def extend (hdis : U ⊓ V = ⊥) (hcover : U ⊔ V = ⊤)
    (s : Γ(U.toScheme, ⊤)) : Γ(X, ⊤) :=
  (existsUnique_pair U V hdis hcover s 0).choose

/-- Extension retains the original full section. -/
theorem extend_left (hdis : U ⊓ V = ⊥) (hcover : U ⊔ V = ⊤)
    (s : Γ(U.toScheme, ⊤)) : U.ι.appTop (extend U V hdis hcover s) = s :=
  (existsUnique_pair U V hdis hcover s 0).choose_spec.1.1

/-- Extension vanishes identically on the complementary open. -/
theorem extend_right (hdis : U ⊓ V = ⊥) (hcover : U ⊔ V = ⊤)
    (s : Γ(U.toScheme, ⊤)) : V.ι.appTop (extend U V hdis hcover s) = 0 :=
  (existsUnique_pair U V hdis hcover s 0).choose_spec.1.2

/-- The complement of a closed open as an actual scheme open. -/
def complement (hU : IsClosed (U : Set X)) : X.Opens := ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩

/-- These actual scheme opens are disjoint. -/
theorem inf_complement (hU : IsClosed (U : Set X)) : U ⊓ complement U hU = ⊥ := by
  ext x
  exact and_not_self_iff _

/-- These actual scheme opens cover the whole source. -/
theorem sup_complement (hU : IsClosed (U : Set X)) : U ⊔ complement U hU = ⊤ := by
  ext x
  exact iff_true_intro (em (x ∈ U))

end FLT.Mazur.SchemeClopenSectionExtension

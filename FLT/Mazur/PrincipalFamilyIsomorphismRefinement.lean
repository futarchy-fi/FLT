/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilySurjective
public import FLT.Mazur.FiniteTypePrincipalIsomorphismDescent

/-!
# Refining an overlap family to genuine coordinate isomorphisms

Surjectivity is first imposed at the common target. Each source is then
quotiented by precisely its map's kernel, retaining the same target and every
refinement square. Existence is proved from the original isomorphisms.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  {a : ∀ i, A i} {b : B}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away b}

omit [Finite ι] in
/-- A surjective lifted family of original injections refines to isomorphisms. -/
theorem exists_principalFamily_bijective_of_surjective
    (hf : ∀ i, Function.Injective (f i)) (x : PrincipalFamilyStage a b f)
    (hx : ∀ i, Function.Surjective (x.hom i)) :
    ∃ y : PrincipalFamilyStage a b f, x ≤ y ∧ y.target = x.target ∧
      ∀ i, Function.Bijective (y.hom i) := by
  choose q hq e he hfac using fun i ↦ exists_principal_lift_equiv
    (a i) b (f i) (hf i) (x.source i) x.target (x.hom i) (hx i) (x.fac i)
  let y : PrincipalFamilyStage a b f :=
    { source := q
      target := x.target
      hom i := (e i).toAlgHom
      fac := hfac }
  refine ⟨y, ⟨hq, le_rfl, fun i ↦ ?_⟩, rfl, fun i ↦ (e i).bijective⟩
  change (e i).toAlgHom.comp (principalTransition (a i) (hq i)) =
    (principalTransition b (le_refl x.target)).comp (x.hom i)
  rw [principalTransition_refl, AlgHom.id_comp]
  exact he i

/-- Every overlap family of original isomorphisms has a genuine isomorphism refinement. -/
theorem exists_principalFamily_bijective (hf : ∀ i, Function.Bijective (f i))
    (x : PrincipalFamilyStage a b f) :
    ∃ y : PrincipalFamilyStage a b f, x ≤ y ∧ ∀ i, Function.Bijective (y.hom i) := by
  obtain ⟨z, hxz, _, hz⟩ := exists_principalFamily_surjective (fun i ↦ (hf i).2) x
  obtain ⟨y, hzy, _, hy⟩ :=
    exists_principalFamily_bijective_of_surjective (fun i ↦ (hf i).1) z hz
  exact ⟨y, hxz.trans hzy, hy⟩

end FLT.Mazur.FiniteTypeRelationModel

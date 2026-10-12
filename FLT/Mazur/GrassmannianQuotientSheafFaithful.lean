/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientSheaf

/-!
# Recovering every original relation from a quotient sheaf

A map commuting with the ambient projections forces inclusion of the complete
relations. An isomorphism commuting with these projections recovers the original
Grassmannian point, rather than only the isomorphism class of its quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] {d : ℕ}
variable (N P : Module.Grassmannian A (A ⊗[R] M) d)

/-- A map of full ambient quotients retains inclusion of every original relation. -/
theorem grassmannianRelation_le_of_quotientSheafMap
    (a : grassmannianQuotientSheaf N ⟶ grassmannianQuotientSheaf P)
    (ha : grassmannianQuotientSheafMap N ≫ a = grassmannianQuotientSheafMap P) :
    N.toSubmodule ≤ P.toSubmodule := by
  let F := tilde.fullyFaithfulFunctor (R := .of A)
  let t := F.preimage a
  have ht : ModuleCat.ofHom N.toSubmodule.mkQ ≫ t =
      ModuleCat.ofHom P.toSubmodule.mkQ := by
    apply F.map_injective
    rw [Functor.map_comp]
    change _ ≫ (tilde.functor (.of A)).map (F.preimage a) = _
    rw [F.map_preimage]
    exact ha
  intro x hx
  have he := congrArg (fun k ↦ k.hom x) ht
  change t.hom (N.toSubmodule.mkQ x) = P.toSubmodule.mkQ x at he
  have hx0 : N.toSubmodule.mkQ x = 0 :=
    (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr hx
  rw [hx0, map_zero] at he
  exact (Submodule.Quotient.mk_eq_zero P.toSubmodule).mp he.symm

/-- An isomorphism respecting the original ambient projections detects the whole point. -/
theorem grassmannianPoint_eq_of_quotientSheafIso
    (e : grassmannianQuotientSheaf N ≅ grassmannianQuotientSheaf P)
    (he : grassmannianQuotientSheafMap N ≫ e.hom = grassmannianQuotientSheafMap P) :
    N = P := by
  apply Module.Grassmannian.ext
  apply le_antisymm
  · exact grassmannianRelation_le_of_quotientSheafMap N P e.hom he
  · apply grassmannianRelation_le_of_quotientSheafMap P N e.inv
    rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Equality of original points is exactly isomorphism of their full ambient quotients. -/
theorem grassmannianPoint_eq_iff_quotientSheafIso :
    N = P ↔ ∃ e : grassmannianQuotientSheaf N ≅ grassmannianQuotientSheaf P,
      grassmannianQuotientSheafMap N ≫ e.hom = grassmannianQuotientSheafMap P := by
  constructor
  · rintro rfl
    exact ⟨Iso.refl _, Category.comp_id _⟩
  · rintro ⟨e, he⟩
    exact grassmannianPoint_eq_of_quotientSheafIso N P e he

end FLT.Mazur.GrassmannianChart

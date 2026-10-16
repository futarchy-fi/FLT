/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameCompletenessTransfer
public import FLT.Mazur.UnramifiedSectionImmersion

/-!
# Complete frames split the actual original geometric fiber

A complete frame gives an isomorphism from the finite coproduct of copies of
the original field spectrum to the whole original fiber. Each component is
exactly its original coordinate morphism. This is a scheme isomorphism, not
only a bijection on geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {K : Type} [Field K] {b : Spec (.of K) ⟶ S}
  (t : Over.mk b ⟶ distinctScheme E I)

/-- Each geometric coordinate is an open section of the entire original fiber. -/
instance geometricCoordinate_isOpenImmersion (i : I) :
    IsOpenImmersion (geometricCoordinate E I t i) :=
  UnramifiedSectionImmersion.isOpenImmersion (pullback.snd E.hom b) _
    (geometricCoordinate_snd E I t i)

/-- Distinct geometric coordinates have disjoint scheme images. -/
theorem geometricCoordinate_disjoint (i j : I) (hij : i ≠ j) :
    Disjoint (Set.range (geometricCoordinate E I t i))
      (Set.range (geometricCoordinate E I t j)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have hx : x = default := Subsingleton.elim _ _
  have hy' : y = default := Subsingleton.elim _ _
  rw [hx, hy'] at hy
  exact hij (geometricCoordinate_point_injective E I t hy.symm)

/-- The original coordinate morphisms assemble into the full fiber comparison. -/
def completeFiberComparison : (∐ fun _ : I ↦ Spec (.of K)) ⟶ pullback E.hom b :=
  Sigma.desc (geometricCoordinate E I t)

omit [Etale E.hom] in
/-- Every component retains the original full relation coordinate. -/
@[reassoc] theorem completeFiberComparison_component (i : I) :
    Sigma.ι (fun _ : I ↦ Spec (.of K)) i ≫ completeFiberComparison E I t =
      geometricCoordinate E I t i := Sigma.ι_comp_desc _ _

/-- The assembled coordinate comparison is an open immersion for any distinct frame. -/
instance completeFiberComparison_isOpenImmersion :
    IsOpenImmersion (completeFiberComparison E I t) :=
  AlgebraicGeometry.isOpenImmersion_sigmaDesc _ (geometricCoordinate E I t)
    (geometricCoordinate_disjoint E I t)

variable (ht : Function.Bijective (fun i ↦ geometricCoordinate E I t i default))

include ht in
/-- Completeness makes the comparison an isomorphism of the whole original fiber. -/
theorem completeFiberComparison_isIso : IsIso (completeFiberComparison E I t) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro x
  obtain ⟨i, hi⟩ := ht.2 x
  refine ⟨(Sigma.ι (fun _ : I ↦ Spec (.of K)) i) default, ?_⟩
  have h := congrArg (fun f : Spec (.of K) ⟶ pullback E.hom b ↦ f default)
    (completeFiberComparison_component E I t i)
  exact h.trans hi

/-- The complete original fiber, with its entire scheme structure, is split by its frame. -/
def completeFiberIso : (∐ fun _ : I ↦ Spec (.of K)) ≅ pullback E.hom b := by
  let _ := completeFiberComparison_isIso E I t ht
  exact asIso (completeFiberComparison E I t)

/-- The fiber isomorphism retains every actual original geometric coordinate. -/
@[reassoc] theorem completeFiberIso_component (i : I) :
    Sigma.ι (fun _ : I ↦ Spec (.of K)) i ≫ (completeFiberIso E I t ht).hom =
      geometricCoordinate E I t i := completeFiberComparison_component E I t i

end FLT.Mazur.RelativeOrderedTuples

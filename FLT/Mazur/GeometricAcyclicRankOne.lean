/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicRankOneRelativeClass
public import FLT.Mazur.ProperLineGlobalRankOneCriterion

/-!
# The geometric acyclic rank-one condition on unrestricted families

Fiber cohomology and fiber section rank define a condition without any
Noetherian hypothesis. It is invariant under relative Picard equivalence
and is preserved by every cartesian base change of a proper family.
On tests with a locally Noetherian model it is the actual direct-image condition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
open SchemePicard (relativeClass mk relativeClass_mk_eq_iff_twist_iso)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- Geometric acyclicity with precisely one section on each actual residue fiber. -/
def GeometricAcyclicRankOne (L : X.Modules) : Prop :=
  ∀ s : S, (∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1))) ∧
    properLineFiberSectionRank f L s = 1

/-- An actual fiber-sheaf isomorphism preserves the dimension of degree-zero cohomology. -/
lemma fiberSectionRank_eq_of_iso {L M : X.Modules} (s : S)
    (a : (pullback (f.fiberι s)).obj L ≅ (pullback (f.fiberι s)).obj M) :
    properLineFiberSectionRank f L s = properLineFiberSectionRank f M s :=
  ((moduleScalarHFunctor (f.fiberToSpecResidueField s) 0).mapIso a).toLinearEquiv.finrank_eq

/-- Actual line isomorphisms preserve the geometric condition. -/
theorem geometricAcyclicRankOne_iso {L M : X.Modules} (a : L ≅ M) :
    GeometricAcyclicRankOne f L ↔ GeometricAcyclicRankOne f M := by
  apply forall_congr'
  intro s
  let b := (pullback (f.fiberι s)).mapIso a
  exact and_congr (forall_congr' fun n ↦
    Equiv.subsingleton_congr (moduleHIsoOfIso b (n + 1)).toEquiv)
      (congrArg (· = 1) (fiberSectionRank_eq_of_iso f s b)).to_iff

/-- Every base-line twist preserves the geometric condition on any base scheme. -/
theorem geometricAcyclicRankOne_baseLineTwist (L : X.Modules) (B : S.Modules)
    (hB : LocallyFreeRankOne B) :
    GeometricAcyclicRankOne f (ModuleSheafTensor.tensor L ((pullback f).obj B)) ↔
      GeometricAcyclicRankOne f L := by
  apply forall_congr'
  intro s
  obtain ⟨b⟩ := baseLineTwist_fiber_iso f L hB s
  exact and_congr (forall_congr' fun n ↦
    Equiv.subsingleton_congr (moduleHIsoOfIso b (n + 1)).toEquiv)
      (congrArg (· = 1) (fiberSectionRank_eq_of_iso f s b)).to_iff

/-- The geometric condition depends only on the actual relative Picard class. -/
theorem geometricAcyclicRankOne_relativeClass_iff {L M : X.Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M)
    (hc : relativeClass f (mk L hL) = relativeClass f (mk M hM)) :
    GeometricAcyclicRankOne f L ↔ GeometricAcyclicRankOne f M := by
  obtain ⟨B, ⟨a⟩⟩ := (relativeClass_mk_eq_iff_twist_iso f hL hM).mp hc
  exact ((geometricAcyclicRankOne_iso f a).trans
    (geometricAcyclicRankOne_baseLineTwist f L B.val B.property)).symm

variable {P T : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
  [IsProper f] (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)

include h hL in
/-- The geometric condition is preserved on every cartesian test, with no Noetherian base. -/
theorem geometricAcyclicRankOne_baseChange (hA : GeometricAcyclicRankOne f L) :
    GeometricAcyclicRankOne q ((pullback p).obj L) := fun t ↦
  ⟨fun n ↦ (properLine_fiber_vanishing_iff h L hL t (n + 1)).mpr ((hA (g t)).1 n),
    (properLineFiberSectionRank_baseChange h L hL t).trans (hA (g t)).2⟩

include h hL in
/-- A locally Noetherian original model identifies geometric and actual direct-image tests. -/
theorem geometricAcyclicRankOne_iff_actual [IsLocallyNoetherian S] [Flat f] :
    GeometricAcyclicRankOne q ((pullback p).obj L) ↔
      AcyclicRankOne q ((pullback p).obj L) := by
  constructor
  · intro hA
    have hv := fun t ↦ (hA t).1
    exact ⟨hv, (properLineAcyclicBaseChanged_rankOne_iff h L hL hv).mpr
      (fun t ↦ (hA t).2)⟩
  · rintro ⟨hv, hn⟩ t
    exact ⟨hv t, (properLineAcyclicBaseChanged_rankOne_iff h L hL hv).mp hn t⟩

end FLT.Mazur.CartierAbel

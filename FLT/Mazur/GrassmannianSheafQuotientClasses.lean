/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientPullback
public import FLT.Mazur.ModuleSheafLocalFrames

/-!
# Isomorphism classes of actual locally free ambient quotients

A representative consists of an actual sheaf, its full ambient epimorphism,
and fixed-rank local frames. Equivalence preserves the entire projection.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R)) (d : ℕ)

/-- An actual locally free rank-d quotient of the original ambient sheaf. -/
structure LocallyFreeSheafQuotient where
  /-- The original quotient sheaf on the source scheme. -/
  sheaf : X.Modules
  /-- The entire ambient projection, retaining all original relations. -/
  projection : grassmannianSchemeAmbient (M := M) β ⟶ sheaf
  epi : Epi projection
  frames : ModuleSheafLocalFrames.HasFrames (ULift.{u} (Fin d)) sheaf

attribute [instance] LocallyFreeSheafQuotient.epi

namespace LocallyFreeSheafQuotient
variable {β d} (P Q S : LocallyFreeSheafQuotient (M := M) β d)

/-- Isomorphisms must preserve the full original quotient projection. -/
def Equivalent : Prop := ∃ e : P.sheaf ≅ Q.sheaf, P.projection ≫ e.hom = Q.projection

/-- Identity preserves all ambient coordinates. -/
theorem equivalent_refl : P.Equivalent P := ⟨Iso.refl _, Category.comp_id _⟩

/-- Reversing a quotient isomorphism preserves the full ambient map. -/
theorem Equivalent.symm {P Q : LocallyFreeSheafQuotient (M := M) β d}
    (h : P.Equivalent Q) : Q.Equivalent P := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he]
  simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Composing quotient isomorphisms preserves every ambient coordinate. -/
theorem Equivalent.trans {P Q S : LocallyFreeSheafQuotient (M := M) β d}
    (h : P.Equivalent Q) (h' : Q.Equivalent S) : P.Equivalent S := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨e ≪≫ e', ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, he, he']

/-- The equivalence relation is full quotient isomorphism, with no choice of atlas. -/
instance quotientSetoid : Setoid (LocallyFreeSheafQuotient (M := M) β d) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, fun h ↦ h.symm, fun h h' ↦ h.trans h'⟩

variable {Y : Scheme.{u}} (g : Y ⟶ X)

/-- Pull back the original sheaf and its entire epimorphism along any scheme map. -/
def pullbackQuotient : LocallyFreeSheafQuotient (M := M) (g ≫ β) d where
  sheaf := (pullback g).obj P.sheaf
  projection := sheafQuotientPullbackMap β g P.projection
  epi := inferInstance
  frames := P.frames.pullback _ _ g

/-- Actual scheme pullback respects full quotient isomorphisms. -/
theorem Equivalent.pullback {P Q : LocallyFreeSheafQuotient (M := M) β d}
    (h : P.Equivalent Q) :
    (P.pullbackQuotient g).Equivalent (Q.pullbackQuotient g) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(Scheme.Modules.pullback g).mapIso e, ?_⟩
  change sheafQuotientPullbackMap β g P.projection ≫ (Scheme.Modules.pullback g).map e.hom =
    sheafQuotientPullbackMap β g Q.projection
  unfold sheafQuotientPullbackMap
  rw [Category.assoc, ← Functor.map_comp, he]

end LocallyFreeSheafQuotient

/-- Classes of actual locally free quotients, modulo full projection-preserving isomorphism. -/
abbrev LocallyFreeSheafQuotientClass :=
  Quotient (LocallyFreeSheafQuotient.quotientSetoid (M := M) (β := β) (d := d))

/-- Arbitrary scheme pullback on original quotient isomorphism classes. -/
def locallyFreeSheafQuotientClassPullback {Y : Scheme.{u}} (g : Y ⟶ X) :
    LocallyFreeSheafQuotientClass (M := M) β d →
      LocallyFreeSheafQuotientClass (M := M) (g ≫ β) d :=
  Quotient.map (fun P ↦ P.pullbackQuotient g) (fun _ _ h ↦ h.pullback g)

end FLT.Mazur.GrassmannianChart

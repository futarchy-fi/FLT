/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDistinctTupleLift
public import FLT.Mazur.QuasiCompactEtaleGeometricSections

/-!
# Complete ordered geometric fibers of the entire etale source

Every geometric fiber of a quasi-compact separated etale morphism has an
actual ordered-point test enumerating its whole geometric pullback. The
original morphism need not be finite. No finite branch or rational subset
of the geometric fiber replaces the original source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {K : Type} [Field K] {b : Spec (.of K) ⟶ S}

/-- Each ordered original coordinate as a point of the complete geometric pullback. -/
def geometricCoordinate (a : Over.mk b ⟶ distinctScheme E I) (i : I) :
    Spec (.of K) ⟶ pullback E.hom b :=
  pullback.lift (a ≫ distinctCoordinate E I i).left (𝟙 _) (by
    rw [Category.id_comp]
    exact (a ≫ distinctCoordinate E I i).w)

omit [Etale E.hom] in
/-- The geometric coordinate retains the actual original arrow. -/
@[reassoc] theorem geometricCoordinate_fst (a : Over.mk b ⟶ distinctScheme E I) (i : I) :
    geometricCoordinate E I a i ≫ pullback.fst E.hom b =
      (a ≫ distinctCoordinate E I i).left := pullback.lift_fst _ _ _

omit [Etale E.hom] in
/-- The coefficient point of each geometric coordinate is unchanged. -/
@[reassoc] theorem geometricCoordinate_snd (a : Over.mk b ⟶ distinctScheme E I) (i : I) :
    geometricCoordinate E I a i ≫ pullback.snd E.hom b = 𝟙 _ := pullback.lift_snd _ _ _

variable [QuasiCompact E.hom] [IsSepClosed K]

/-- An actual ordered-point test enumerates every point of the full geometric fiber exactly once. -/
theorem exists_complete_geometric_tuple (b : Spec (.of K) ⟶ S) :
    ∃ (n : ℕ) (a : Over.mk b ⟶ distinctScheme E (Fin n)),
      Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) a i default) := by
  let _ : Subsingleton (Over.mk b).left := inferInstanceAs (Subsingleton (Spec (.of K)))
  obtain ⟨n, s, hs, hi, hr⟩ :=
    QuasiCompactEtaleGeometricSections.exists_geometric_sections E.hom b
  let r (i : Fin n) : Over.mk b ⟶ E := Over.homMk (s i ≫ pullback.fst E.hom b) (by
    change (s i ≫ pullback.fst E.hom b) ≫ E.hom = b
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp])
  have hri : Function.Injective r := by
    intro i j hij
    apply hi
    apply congrArg (fun z : Spec (.of K) ⟶ pullback E.hom b ↦ z default)
    apply pullback.hom_ext
    · exact congrArg Over.Hom.left hij
    · rw [hs, hs]
  let a : Over.mk b ⟶ distinctScheme E (Fin n) := distinctLift E (Fin n) r hri
  have hac (i : Fin n) : geometricCoordinate E (Fin n) a i = s i := by
    apply pullback.hom_ext
    · rw [geometricCoordinate_fst]
      exact congrArg Over.Hom.left (distinctLift_coordinate E (Fin n) r hri i)
    · rw [geometricCoordinate_snd, hs]
  refine ⟨n, a, ?_⟩
  simpa only [hac, Function.Bijective] using And.intro hi hr

end FLT.Mazur.RelativeOrderedTuples

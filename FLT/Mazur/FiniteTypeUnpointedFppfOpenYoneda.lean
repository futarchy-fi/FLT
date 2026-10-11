/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeUnpointedFppfOpenRepresentation
public import Mathlib.CategoryTheory.Yoneda

/-!
# A Yoneda representation of unpointed acyclic chart intersections

The subfunctor of a test's functor of points consisting of locally acyclic
restrictions is naturally represented by the actual descended open scheme.
The representing transformation is the original open immersion on every test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The actual subfunctor of maps on which the supplied section is locally acyclic. -/
def finiteTypeFppfAcyclicTestSubfunctor : Subfunctor (yoneda.obj T) where
  obj U := {b | (relativeFppfSheaf f).obj.map b.op s ∈
    (localGeometricAcyclicFppfSubfunctor f).obj U}
  map {U V} g b hb := by
    have h := (localGeometricAcyclicFppfSubfunctor f).map g hb
    change (relativeFppfSheaf f).obj.map g
      ((relativeFppfSheaf f).obj.map b.op s) ∈
        (localGeometricAcyclicFppfSubfunctor f).obj V at h
    change (relativeFppfSheaf f).obj.map (g.unop ≫ b).op s ∈
      (localGeometricAcyclicFppfSubfunctor f).obj V
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      Quiver.Hom.op_unop] using h

/-- Each map from the actual open supplies a map whose restricted section is locally acyclic. -/
def finiteTypeFppfOpenYonedaMap (U : Over (Spec (.of R)))
    (k : U ⟶ finiteTypeUnpointedFppfOpenTest f T s) :
    (finiteTypeFppfAcyclicTestSubfunctor f T s).toFunctor.obj (op U) := by
  refine ⟨k ≫ finiteTypeUnpointedFppfOpenArrow f T s, ?_⟩
  apply (finiteTypeUnpointedFppfAcyclicOpen_represents_over f _ s).mpr
  refine ⟨k, rfl, ?_⟩
  intro l hl
  apply Over.OverMorphism.ext
  apply (cancel_mono (finiteTypeUnpointedFppfAcyclicOpen f T s).ι).mp
  exact congrArg Over.Hom.left hl

/-- The open scheme represents the actual acyclic subfunctor on each test. -/
def finiteTypeFppfOpenYonedaEquiv (U : Over (Spec (.of R))) :
    (U ⟶ finiteTypeUnpointedFppfOpenTest f T s) ≃
      (finiteTypeFppfAcyclicTestSubfunctor f T s).toFunctor.obj (op U) :=
  Equiv.ofBijective (finiteTypeFppfOpenYonedaMap f T s U) ⟨by
    intro k l h
    apply Over.OverMorphism.ext
    apply (cancel_mono (finiteTypeUnpointedFppfAcyclicOpen f T s).ι).mp
    exact congrArg (fun b ↦ b.val.left) h, by
    intro b
    obtain ⟨k, hk, _⟩ := (finiteTypeUnpointedFppfAcyclicOpen_represents_over f b.val s).mp
      b.property
    exact ⟨k, Subtype.ext hk⟩⟩

/-- The representation is natural for every original relative test morphism. -/
def finiteTypeFppfOpenYonedaIso :
    yoneda.obj (finiteTypeUnpointedFppfOpenTest f T s) ≅
      (finiteTypeFppfAcyclicTestSubfunctor f T s).toFunctor :=
  NatIso.ofComponents (fun U ↦ (finiteTypeFppfOpenYonedaEquiv f T s U.unop).toIso)
    (fun {U V} g ↦ by
      apply ConcreteCategory.hom_ext
      intro k
      exact Subtype.ext (Category.assoc g.unop k (finiteTypeUnpointedFppfOpenArrow f T s)))

/-- The representing map is exactly the original open inclusion after forgetting membership. -/
lemma finiteTypeFppfOpenYonedaIso_inclusion :
    (finiteTypeFppfOpenYonedaIso f T s).hom ≫ (finiteTypeFppfAcyclicTestSubfunctor f T s).ι =
      yoneda.map (finiteTypeUnpointedFppfOpenArrow f T s) := rfl

end FLT.Mazur.CartierAbel

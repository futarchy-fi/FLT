/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedAcyclicDegreeOpen

/-!
# Natural representation of the degree-d Picard chart on each test

The actual degree chart represents the inverse image of the degree-d Picard
subfunctor under every original test section. The representing transformation
is precisely the open immersion into that test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T)) (d : ℕ)

/-- The inverse image of the original degree-d Picard subfunctor on an arbitrary test. -/
def acyclicDegreePicardTestSubfunctor : Subfunctor (yoneda.obj T) where
  obj U := {b | (relativeFppfSheaf f).obj.map b.op s ∈
    (acyclicDegreePicardSubfunctor f d).obj U}
  map {U V} g b hb := by
    have h := (acyclicDegreePicardSubfunctor f d).map g hb
    change (relativeFppfSheaf f).obj.map g
      ((relativeFppfSheaf f).obj.map b.op s) ∈
        (acyclicDegreePicardSubfunctor f d).obj V at h
    change (relativeFppfSheaf f).obj.map (g.unop ≫ b).op s ∈
      (acyclicDegreePicardSubfunctor f d).obj V
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      Quiver.Hom.op_unop] using h

/-- The map from the actual degree chart to the subfunctor on each original test. -/
def unpointedDegreeYonedaMap (U : Over (Spec (.of R)))
    (k : U ⟶ unpointedAcyclicDegreeTest f T s d) :
    (acyclicDegreePicardTestSubfunctor f T s d).toFunctor.obj (op U) :=
  ⟨k ≫ unpointedAcyclicDegreeArrow f T s d,
    (unpointedAcyclicDegreeOpen_represents f T s d _).mpr
      ⟨k, rfl, fun _l hl ↦ (cancel_mono (unpointedAcyclicDegreeArrow f T s d)).mp hl⟩⟩

/-- All maps into the actual degree chart are exactly all degree-d restrictions. -/
def unpointedDegreeYonedaEquiv (U : Over (Spec (.of R))) :
    (U ⟶ unpointedAcyclicDegreeTest f T s d) ≃
      (acyclicDegreePicardTestSubfunctor f T s d).toFunctor.obj (op U) :=
  Equiv.ofBijective (unpointedDegreeYonedaMap f T s d U) ⟨by
    intro k l h
    exact (cancel_mono (unpointedAcyclicDegreeArrow f T s d)).mp (congrArg Subtype.val h), by
    intro b
    obtain ⟨k, hk, _⟩ := (unpointedAcyclicDegreeOpen_represents f T s d b.val).mp b.property
    exact ⟨k, Subtype.ext hk⟩⟩

/-- The actual degree chart naturally represents the inverse-image Picard subfunctor. -/
def unpointedDegreeYonedaIso :
    yoneda.obj (unpointedAcyclicDegreeTest f T s d) ≅
      (acyclicDegreePicardTestSubfunctor f T s d).toFunctor :=
  NatIso.ofComponents (fun U ↦ (unpointedDegreeYonedaEquiv f T s d U.unop).toIso)
    (fun {U V} g ↦ by
      apply ConcreteCategory.hom_ext
      intro k
      exact Subtype.ext (Category.assoc g.unop k (unpointedAcyclicDegreeArrow f T s d)))

/-- Forgetting membership recovers the original open immersion, exactly. -/
lemma unpointedDegreeYonedaIso_inclusion :
    (unpointedDegreeYonedaIso f T s d).hom ≫ (acyclicDegreePicardTestSubfunctor f T s d).ι =
      yoneda.map (unpointedAcyclicDegreeArrow f T s d) := rfl

end FLT.Mazur.CartierAbel

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeUnpointedFppfOpenRepresentation
public import FLT.Mazur.SubfunctorRepresentedPullback
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# The unpointed acyclic inclusion is represented by open immersions

Every morphism from a representable test into the actual Picard sheaf has
an actual cartesian square with the local acyclic inclusion. Its representing
arrow is the descended scheme open immersion. No original section is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

instance finiteTypeUnpointedFppfOpenArrow_isOpenImmersion (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    IsOpenImmersion (finiteTypeUnpointedFppfOpenArrow f T s).left :=
  inferInstanceAs (IsOpenImmersion (finiteTypeUnpointedFppfAcyclicOpen f T s).ι)

instance finiteTypeUnpointedFppfOpenArrow_mono (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    Mono (finiteTypeUnpointedFppfOpenArrow f T s) :=
  Over.mono_of_mono_left _

/-- The representing open carries the original restricted section in the actual subsheaf. -/
def finiteTypeLocalAcyclicOpenLift (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    uliftYoneda.{1}.obj (finiteTypeUnpointedFppfOpenTest f T s) ⟶
      (localGeometricAcyclicFppfSubfunctor f).toFunctor :=
  PicardOpenRepresentation.lift (localGeometricAcyclicFppfSubfunctor f)
    (finiteTypeUnpointedFppfOpenArrow f T s) s
    (fun b ↦ finiteTypeUnpointedFppfAcyclicOpen_represents_over f b s)

/-- The explicit open-immersion square is cartesian in the actual presheaf category. -/
theorem finiteTypeLocalAcyclicOpen_isPullback (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    IsPullback (finiteTypeLocalAcyclicOpenLift f T s)
      (uliftYoneda.{1}.map (finiteTypeUnpointedFppfOpenArrow f T s))
      (localGeometricAcyclicFppfSubfunctor f).ι (uliftYonedaEquiv.symm s) :=
  PicardOpenRepresentation.isPullback (localGeometricAcyclicFppfSubfunctor f)
    (finiteTypeUnpointedFppfOpenArrow f T s) s
    (fun b ↦ finiteTypeUnpointedFppfAcyclicOpen_represents_over f b s)

/-- All representable tests of the actual inclusion are represented by scheme open immersions. -/
theorem finiteTypeLocalAcyclicInclusion_open_tests
    {T : Over (Spec (.of R))}
    (g : uliftYoneda.{1}.obj T ⟶ (relativeFppfSheaf f).obj ⋙ forget CommGrpCat) :
    ∃ (U : Over (Spec (.of R))) (j : U ⟶ T), IsOpenImmersion j.left ∧
      ∃ k : uliftYoneda.{1}.obj U ⟶ (localGeometricAcyclicFppfSubfunctor f).toFunctor,
        IsPullback k (uliftYoneda.{1}.map j) (localGeometricAcyclicFppfSubfunctor f).ι g := by
  obtain ⟨s, rfl⟩ := uliftYonedaEquiv.symm.surjective g
  exact ⟨finiteTypeUnpointedFppfOpenTest f T s, finiteTypeUnpointedFppfOpenArrow f T s,
    inferInstance, finiteTypeLocalAcyclicOpenLift f T s,
    finiteTypeLocalAcyclicOpen_isPullback f T s⟩

/-- The actual local acyclic inclusion is a relatively representable presheaf morphism. -/
theorem finiteTypeLocalAcyclicInclusion_representable :
    uliftYoneda.{1}.relativelyRepresentable (localGeometricAcyclicFppfSubfunctor f).ι := by
  intro T g
  obtain ⟨U, j, _, k, h⟩ := finiteTypeLocalAcyclicInclusion_open_tests f g
  exact ⟨U, j, k, h⟩

/-- Every representation of every test pullback is an open immersion, intrinsically. -/
theorem finiteTypeLocalAcyclicInclusion_representableOpen :
    ((@IsOpenImmersion : MorphismProperty Scheme.{0}).inverseImage
      (Over.forget (Spec (.of R)))).relative uliftYoneda.{1}
        (localGeometricAcyclicFppfSubfunctor f).ι := by
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨U, j, hj, k, h⟩ := finiteTypeLocalAcyclicInclusion_open_tests f g
  exact ⟨U, k, j, h, hj⟩

end FLT.Mazur.CartierAbel

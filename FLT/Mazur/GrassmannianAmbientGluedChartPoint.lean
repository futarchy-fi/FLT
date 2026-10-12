/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientOverlapFactorization
public import FLT.Mazur.GrassmannianAmbientGluedBase

/-!
# Choice-independent ambient chart classifications in the glued scheme

The two classifying maps of any original double-chart point become literally
equal in the glued scheme. This gives compatibility for any chart choices
representing the same original quotient, and commutes with coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- The classifying morphism of an original chart point into the constructed glued scheme. -/
def ambientGluedChartPoint (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d :=
  ((ambientChartSchemePointEquiv i).symm N).val ≫ ambientGrassmannianChart R M κ d i

/-- The classifying morphism preserves the original coefficient base. -/
@[reassoc] theorem ambientGluedChartPoint_over (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    ambientGluedChartPoint i N ≫ ambientGrassmannianStructure R M κ d =
      Spec.algebraMap R A := by
  rw [ambientGluedChartPoint, Category.assoc, ambientGrassmannianChart_over]
  exact ((ambientChartSchemePointEquiv i).symm N).property

/-- The classifications of every original double-chart point agree in the glued scheme. -/
theorem ambientGluedChartPoint_overlap (i j : AmbientChartIndex R M κ d)
    (N : AmbientOverlapPoint (A := A) i j) :
    ambientGluedChartPoint i N.val =
      ambientGluedChartPoint j (ambientOverlapSecondChartPoint i j N) := by
  have hi := congrArg Subtype.val (ambientOverlapClassifyingHom_first i j N)
  have hj := congrArg Subtype.val (ambientOverlapClassifyingHom_second i j N)
  let f : Spec (.of A) ⟶ indexedOverlapScheme i j :=
    Spec.map (CommRingCat.ofHom (ambientOverlapClassifyingHom i j N).toRingHom)
  change f ≫ indexedOverlapInclusion i j = _ at hi
  change f ≫ indexedChartTransition i j = _ at hj
  rw [ambientGluedChartPoint, ambientGluedChartPoint, ← hi, ← hj, Category.assoc,
    Category.assoc, ambientGrassmannianChart_overlap]

/-- Arbitrary chart choices for the same entire original quotient give the same morphism. -/
theorem ambientGluedChartPoint_eq (i j : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i))
    (P : AmbientChartPoint (ambientChartBaseChange A j)) (h : N.val = P.val) :
    ambientGluedChartPoint i N = ambientGluedChartPoint j P := by
  have hj : Function.Bijective (N.val.toSubmodule.mkQ.comp
      (ambientChartSelected (ambientChartBaseChange A j))) := by
    rw [h]
    exact P.property
  let Q : AmbientOverlapPoint (A := A) i j := ⟨N, hj⟩
  have he : ambientOverlapSecondChartPoint i j Q = P := Subtype.ext h
  exact (ambientGluedChartPoint_overlap i j Q).trans (congrArg (ambientGluedChartPoint j) he)

/-- Classification in the glued scheme commutes with every coefficient homomorphism. -/
theorem ambientGluedChartPoint_natural (f : A →ₐ[R] B) (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    ambientGluedChartPoint i (ambientChartMap f i N) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ambientGluedChartPoint i N := by
  unfold ambientGluedChartPoint
  rw [ambientChartSchemePointEquiv_symm_natural]
  exact Category.assoc _ _ _

/-- Equal original functor images have compatible classifications after different maps. -/
theorem ambientGluedChartPoint_map_eq {C : Type u} [CommRing C] [Algebra R C]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) (i j : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i))
    (P : AmbientChartPoint (ambientChartBaseChange B j))
    (h : Module.Grassmannian.map f N.val = Module.Grassmannian.map g P.val) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ambientGluedChartPoint i N =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ ambientGluedChartPoint j P := by
  rw [← ambientGluedChartPoint_natural, ← ambientGluedChartPoint_natural]
  exact ambientGluedChartPoint_eq i j _ _ h

end FLT.Mazur.GrassmannianChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientGluedChartPoint
public import FLT.Mazur.AffineMorphismAlgebraMap

/-!
# Original quotient classifications agree on arbitrary common scheme tests

Agreement of actual Grassmannian scalar extensions implies equality of the local
classifying morphisms on a full scheme intersection. Affine charts of the test
scheme recover the coefficient maps, so no reducedness assumption is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B C M κ : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Classifications of two scalar extensions agree on every common coefficient algebra. -/
theorem ambientGluedChartPoint_commonAlgebra {D : Type u} [CommRing D] [Algebra R D]
    (s : A →ₐ[R] B) (t : A →ₐ[R] C) (f : B →ₐ[R] D) (g : C →ₐ[R] D)
    (N : Module.Grassmannian A (A ⊗[R] M) d) (i j : AmbientChartIndex R M κ d)
    (P : AmbientChartPoint (ambientChartBaseChange B i))
    (Q : AmbientChartPoint (ambientChartBaseChange C j))
    (hP : P.val = Module.Grassmannian.map s N) (hQ : Q.val = Module.Grassmannian.map t N)
    (h : f.comp s = g.comp t) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ambientGluedChartPoint i P =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ ambientGluedChartPoint j Q := by
  apply ambientGluedChartPoint_map_eq
  rw [hP, hQ, ← Module.Grassmannian.map_comp, ← Module.Grassmannian.map_comp, h]

/-- Any common scheme test of two localizations has equal original quotient classifications. -/
theorem ambientGluedChartPoint_commonTest
    (s : A →ₐ[R] B) (t : A →ₐ[R] C)
    (N : Module.Grassmannian A (A ⊗[R] M) d) (i j : AmbientChartIndex R M κ d)
    (P : AmbientChartPoint (ambientChartBaseChange B i))
    (Q : AmbientChartPoint (ambientChartBaseChange C j))
    (hP : P.val = Module.Grassmannian.map s N) (hQ : Q.val = Module.Grassmannian.map t N)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) (g : X ⟶ Spec (.of C))
    (h : f ≫ Spec.map (CommRingCat.ofHom s.toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom t.toRingHom)) :
    f ≫ ambientGluedChartPoint i P = g ≫ ambientGluedChartPoint j Q := by
  apply X.affineOpenCover.openCover.hom_ext
  intro a
  let D := X.affineOpenCover.X a
  let k : Spec (.of D) ⟶ X := X.affineOpenCover.f a
  let z := (k ≫ f) ≫ Spec.algebraMap R B
  let _ : Algebra R D := (Spec.preimage z).hom.toAlgebra
  have hz : Spec.algebraMap R D = z := Spec.map_preimage _
  have hs : Spec.map (CommRingCat.ofHom s.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R B := by
    rw [Spec.algebraMap, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext s.comp_algebraMap)
  have ht : Spec.map (CommRingCat.ofHom t.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R C := by
    rw [Spec.algebraMap, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext t.comp_algebraMap)
  have hf : (k ≫ f) ≫ Spec.algebraMap R B = Spec.algebraMap R D := hz.symm
  have hg : (k ≫ g) ≫ Spec.algebraMap R C = Spec.algebraMap R D := by
    rw [← ht, Category.assoc, ← Category.assoc g, ← h, Category.assoc f, hs]
    exact (Category.assoc k f _).symm.trans hf
  let F := affineOverAlgHom R B D (k ≫ f) hf
  let G := affineOverAlgHom R C D (k ≫ g) hg
  have hF : Spec.map (CommRingCat.ofHom F.toRingHom) = k ≫ f :=
    affineOverAlgHom_spec R B D _ hf
  have hG : Spec.map (CommRingCat.ofHom G.toRingHom) = k ≫ g :=
    affineOverAlgHom_spec R C D _ hg
  have hc : F.comp s = G.comp t := by
    apply AlgHom.ext
    have he : CommRingCat.ofHom (F.comp s).toRingHom =
        CommRingCat.ofHom (G.comp t).toRingHom := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom s.toRingHom ≫ CommRingCat.ofHom F.toRingHom) =
        Spec.map (CommRingCat.ofHom t.toRingHom ≫ CommRingCat.ofHom G.toRingHom)
      rw [Spec.map_comp, Spec.map_comp, hF, hG, Category.assoc, Category.assoc, h]
    exact fun x ↦ congrArg (fun e : CommRingCat.of A ⟶ CommRingCat.of D ↦ e x) he
  have he := ambientGluedChartPoint_commonAlgebra s t F G N i j P Q hP hQ hc
  rw [hF, hG, Category.assoc, Category.assoc] at he
  exact he

end FLT.Mazur.GrassmannianChart

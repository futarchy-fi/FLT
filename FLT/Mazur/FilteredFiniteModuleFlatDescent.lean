/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredMatrixFlatDescent
public import FLT.Mazur.FiniteModuleMatrixPresentation

/-!
# Uniform flatness descent for an original finitely presented module

A fixed finitely presented module whose actual scalar extension is flat at
the colimit becomes flat at one finite stage and remains flat after every
later transition. Its matrix presentation is constructed, not assumed.
The finiteness here is module finite presentation over the base ring.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.Approximation

/-- Flatness of the actual scalar extension along a specified ring map. -/
def ScalarFlat {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  let _ := φ.toAlgebra
  Module.Flat S (S ⊗[R] M)

universe u v w
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat)]

include hc in
/-- One actual coefficient stage controls every relation of the original finite module. -/
theorem exists_flat_finite_module_stage (i : I) (M : Type*) [AddCommGroup M]
    [Module (F.obj i) M] [Module.FinitePresentation (F.obj i) M]
    (h : ScalarFlat (c.ι.app i).hom M) :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k),
      ScalarFlat (F.map (g ≫ e)).hom M := by
  obtain ⟨m, n, A, ⟨a⟩⟩ := MatrixCokernel.exists_matrix_presentation
    (R := F.obj i) (M := M)
  have hA : Module.Flat c.pt ((Fin m → c.pt) ⧸
      LinearMap.range (A.map (c.ι.app i).hom).mulVecLin) := by
    let _ : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
    exact (MatrixCokernel.flat_tensor_iff_matrix c.pt A a).mp h
  obtain ⟨j, g, hg⟩ := exists_flat_matrix_stage F c hc i A hA
  refine ⟨j, g, fun k e ↦ ?_⟩
  let _ := (F.map (g ≫ e)).hom.toAlgebra
  exact (MatrixCokernel.flat_tensor_iff_matrix (F.obj k) A a).mpr (hg k e)

end FLT.Mazur.Approximation

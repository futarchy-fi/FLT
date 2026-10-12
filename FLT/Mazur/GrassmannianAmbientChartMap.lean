/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartPoints
public import FLT.Mazur.GrassmannianFunctorLocalizedChart

/-!
# Original ambient charts are stable under coefficient maps

A selected quotient basis stays a basis under every coefficient algebra map.
Consequently the actual Grassmannian functor restricts to each original chart.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Every coefficient map preserves membership in an original ambient chart. -/
theorem ambientChart_map_bijective (f : A →ₐ[R] B) (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    Function.Bijective ((Module.Grassmannian.map f N.val).toSubmodule.mkQ.comp
      (ambientChartSelected (ambientChartBaseChange B i))) := by
  let _ : Algebra A B := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  have hf : f = IsScalarTower.toAlgHom R A B := by ext; rfl
  rw [hf]
  apply grassmannian_map_selected_bijective
  rw [baseChangeMkQ_selected_map]
  let e := LinearEquiv.ofBijective _ N.property
  let b := (Pi.basisFun A (Fin d)).map e
  apply selectedColumnMap_bijective_of_basis _ (b.baseChange B)
  intro j
  rw [Module.Basis.baseChange_apply]
  rfl

/-- The restriction uses exactly the original Grassmannian map, with its full relation. -/
def ambientChartMap (f : A →ₐ[R] B) (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    AmbientChartPoint (ambientChartBaseChange B i) :=
  ⟨Module.Grassmannian.map f N.val, ambientChart_map_bijective f i N⟩

/-- Forgetting chart membership recovers the actual Grassmannian functor image. -/
@[simp] theorem ambientChartMap_val (f : A →ₐ[R] B) (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    (ambientChartMap f i N).val = Module.Grassmannian.map f N.val := rfl

/-- Identity coefficient maps act identically on the original chart. -/
@[simp] theorem ambientChartMap_id (i : AmbientChartIndex R M κ d)
    (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    ambientChartMap (AlgHom.id R A) i N = N := by
  apply Subtype.ext
  exact Module.Grassmannian.map_id d (.of R A) N.val

variable {C : Type u} [CommRing C] [Algebra R C]

/-- Restriction to a chart respects arbitrary compositions of coefficient maps. -/
theorem ambientChartMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (i : AmbientChartIndex R M κ d) (N : AmbientChartPoint (ambientChartBaseChange A i)) :
    ambientChartMap (g.comp f) i N = ambientChartMap g i (ambientChartMap f i N) := by
  apply Subtype.ext
  exact Module.Grassmannian.map_comp d f g N.val

end FLT.Mazur.GrassmannianChart

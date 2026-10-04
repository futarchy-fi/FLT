/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackIdeal
public import FLT.Mazur.FlatIdealTensor
public import FLT.Mazur.IdealModuleSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Affine sections of flat ideal pullback

For a flat morphism and compatible affine opens, extension of scalars of the
actual ideal-module sections is the module of sections of the comap ideal.
The formula on pure tensors identifies the comparison with multiplication of
sections, and gives finite-presentation descent for a faithfully flat affine map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- The affine tensor comparison for the actual comap ideal module. -/
def idealModuleAffineTensorEquiv (I : Y.IdealSheafData) (f : X ⟶ Y) [Flat f]
    (V : Y.affineOpens) (U : X.affineOpens) (h : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI := (f.appLE V U h).hom.toAlgebra
    Γ(X, U) ⊗[Γ(Y, V)] Γ(idealModule I, V.1) ≃ₗ[Γ(X, U)]
      Γ(idealModule (I.comap f), U.1) := by
  letI := (f.appLE V U h).hom.toAlgebra
  letI : Module.Flat Γ(Y, V) Γ(X, U) := f.flat_appLE V.2 U.2 h
  exact LinearEquiv.baseChange Γ(Y, V) Γ(X, U) _ _ (idealModuleAffineEquiv I V) ≪≫ₗ
    flatIdealTensorEquiv (I.ideal V) ≪≫ₗ
    LinearEquiv.ofEq _ _ (I.ideal_comap f V U h).symm ≪≫ₗ
    (idealModuleAffineEquiv (I.comap f) U).symm

/-- The comparison extends the ideal inclusion along the actual affine section map. -/
lemma idealModuleAffineTensorEquiv_tmul (I : Y.IdealSheafData) (f : X ⟶ Y) [Flat f]
    (V : Y.affineOpens) (U : X.affineOpens) (h : U.1 ≤ f ⁻¹ᵁ V.1)
    (a : Γ(X, U)) (s : Γ(idealModule I, V.1)) :
    letI := (f.appLE V U h).hom.toAlgebra
    (idealModuleι (I.comap f)).app U.1
      (idealModuleAffineTensorEquiv I f V U h (a ⊗ₜ[Γ(Y, V)] s)) =
        a * f.appLE V U h ((idealModuleι I).app V.1 s) := by
  let := (f.appLE V U h).hom.toAlgebra
  rw [← idealModuleAffineEquiv_val]
  simp only [idealModuleAffineTensorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.coe_ofEq_apply, flatIdealTensorEquiv_val, idealTensorInclusion_tmul,
    idealModuleAffineEquiv_val]
  rfl

/-- On affine schemes, finite presentation of a pulled-back ideal descends along
an actual flat surjective morphism. -/
theorem idealModule_finitePresentation_of_flat_surjective
    [IsAffine X] [IsAffine Y] (I : Y.IdealSheafData) (f : X ⟶ Y)
    [Flat f] [Surjective f]
    [Module.FinitePresentation Γ(X, ⊤) Γ(idealModule (I.comap f), ⊤)] :
    Module.FinitePresentation Γ(Y, ⊤) Γ(idealModule I, ⊤) := by
  let := f.appTop.hom.toAlgebra
  let : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (f := f)).mp
      ⟨inferInstance, inferInstance⟩
  let : Module.FinitePresentation Γ(X, ⊤)
      ((I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩) :=
    Module.FinitePresentation.of_equiv
      (idealModuleAffineEquiv (I.comap f) ⟨⊤, isAffineOpen_top X⟩)
  have : Module.FinitePresentation Γ(X, ⊤)
      ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom) := by
    rw [← I.ideal_comap_top f]
    infer_instance
  let : Module.FinitePresentation Γ(Y, ⊤) (I.ideal ⟨⊤, isAffineOpen_top Y⟩) :=
    ideal_finitePresentation_of_faithfullyFlat (S := Γ(X, ⊤)) _
  exact Module.FinitePresentation.of_equiv
    (idealModuleAffineEquiv I ⟨⊤, isAffineOpen_top Y⟩).symm

end FLT.Mazur.FCurve

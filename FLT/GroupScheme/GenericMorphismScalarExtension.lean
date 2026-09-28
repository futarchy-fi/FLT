/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatScalarExtension
public import FLT.GroupScheme.PadicBialgebraDescent

/-!
# Generic morphisms under scalar extension

The scalar extension of a generic morphism is a morphism between the actual
base-changed models. Its coordinate formula lets arithmetic descent compare
away and local lifts of the same rational morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsFractionRing R K]
    (S L : Type) [CommRing S] [Field L] [Algebra R S]
    [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]

/-- Extend a generic map to the geometric points of the base-changed models. -/
def GenericGaloisHom.scalarExtension {X Y : FF R K} (f : GenericGaloisHom X Y) :
    GenericGaloisHom (X.scalarExtension S L) (Y.scalarExtension S L) :=
  BialgHom.precompPoints (f.scalarExtensionBialgHom S L)

omit [PerfectField K] [IsFractionRing R K] in
/-- On original coordinates, the generic comparison identifies the two
successive scalar extensions. -/
@[simp] theorem FF.scalarExtensionGenericEquiv_tmul (X : FF R K)
    (l : L) (s : S) (x : X.CoordinateRing) :
    X.scalarExtensionGenericEquiv S L (l ⊗ₜ[S] (s ⊗ₜ[R] x)) =
      (l * algebraMap S L s) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] x) := by
  change (Algebra.TensorProduct.cancelBaseChange R K L L X.CoordinateRing).symm
    ((Algebra.TensorProduct.cancelBaseChange R S L L X.CoordinateRing)
      (l ⊗ₜ[S] (s ⊗ₜ[R] x))) = _
  apply (Algebra.TensorProduct.cancelBaseChange R K L L X.CoordinateRing).injective
  simp [Algebra.smul_def, mul_comm]

/-- The generic coordinate map of the extended point map is the prescribed
scalar extension of the original generic coordinate map. -/
theorem GenericGaloisHom.toBialgHom_scalarExtension [PerfectField L]
    {X Y : FF R K} (f : GenericGaloisHom X Y) :
    (f.scalarExtension S L).toBialgHom = f.scalarExtensionBialgHom S L := by
  ext a
  apply (GaloisModule.GenericFiber.genericEvalAlgEquiv L (AlgebraicClosure L)
    (L ⊗[S] (X.scalarExtension S L).CoordinateRing)).injective
  ext p
  have h := (f.scalarExtension S L).toBialgHom_points (Additive.ofMul p)
  exact AlgHom.congr_fun (congrArg Additive.toMul h) a

/-- Cancellation expresses the coordinate value in the common generic field,
independently of the intermediate integral coefficient ring. -/
theorem GenericGaloisHom.scalarExtensionBialgHom_cancel
    {X Y : FF R K} (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) :
    bialgebraCancelBaseChange R S L X.CoordinateRing
        (f.scalarExtensionBialgHom S L (1 ⊗ₜ[S] (1 ⊗ₜ[R] y))) =
      PadicPatching.scalarExtensionMap K L X.CoordinateRing
        (f.toBialgHom (1 ⊗ₜ[R] y)) := by
  change bialgebraCancelBaseChange R S L X.CoordinateRing
    ((X.scalarExtensionGenericEquiv S L).symm
      ((Bialgebra.TensorProduct.map (BialgHom.id L L) f.toBialgHom)
        (Y.scalarExtensionGenericEquiv S L (1 ⊗ₜ[S] (1 ⊗ₜ[R] y))))) = _
  rw [FF.scalarExtensionGenericEquiv_tmul]
  simp only [map_one, mul_one]
  change (Algebra.TensorProduct.cancelBaseChange R S L L X.CoordinateRing)
    ((Algebra.TensorProduct.cancelBaseChange R S L L X.CoordinateRing).symm
      ((Algebra.TensorProduct.cancelBaseChange R K L L X.CoordinateRing)
        (1 ⊗ₜ[K] f.toBialgHom (1 ⊗ₜ[R] y)))) = _
  rw [AlgEquiv.apply_symm_apply]
  generalize f.toBialgHom (1 ⊗ₜ[R] y) = z
  induction z using TensorProduct.inductionOn with
  | tmul k x => simp [Algebra.smul_def]
  | add a b ha hb => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) ha hb

/-- Cancellation of a lifted integral map is scalar extension of its value. -/
theorem ModelHom.scalarExtension_cancel [PerfectField L]
    {X Y : FF R K} (g : ModelHom (X.scalarExtension S L) (Y.scalarExtension S L))
    (f : GenericGaloisHom X Y) (hg : genericHom g = f.scalarExtension S L)
    (y : Y.CoordinateRing) :
    PadicPatching.scalarExtensionMap S L X.CoordinateRing (g (1 ⊗ₜ[R] y)) =
      PadicPatching.scalarExtensionMap K L X.CoordinateRing
        (f.toBialgHom (1 ⊗ₜ[R] y)) := by
  have h := congrArg (fun h : GenericGaloisHom (X.scalarExtension S L)
      (Y.scalarExtension S L) ↦ h.toBialgHom) hg
  rw [g.toBialgHom_genericHom, f.toBialgHom_scalarExtension S L] at h
  have he := congrArg (fun t ↦ bialgebraCancelBaseChange R S L X.CoordinateRing
    (t (1 ⊗ₜ[S] (1 ⊗ₜ[R] y)))) h
  rw [f.scalarExtensionBialgHom_cancel S L] at he
  convert he using 1
  change PadicPatching.scalarExtensionMap S L X.CoordinateRing (g (1 ⊗ₜ[R] y)) =
    (Algebra.TensorProduct.cancelBaseChange R S L L X.CoordinateRing)
      (1 ⊗ₜ[S] g (1 ⊗ₜ[R] y))
  generalize g (1 ⊗ₜ[R] y) = z
  induction z using TensorProduct.inductionOn with
  | tmul s x => simp [Algebra.smul_def]
  | add a b ha hb => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) ha hb

end ThreeAdicPlan

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDualPullback
public import FLT.Mazur.DivisorCanonicalSection
public import FLT.Mazur.ModuleGlobalSectionPullback
/-!
# Cancellation and transition from a canonical section

A regular dual evaluation detects scalar equality after pullback. For Cartier
divisors on affine charts, flatness preserves the required regularity. Thus a
canonical-section transition determines the transition of arbitrary sections.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme.{u}}
/-- A regular pulled-back dual evaluation cancels scalars. -/
lemma pullGlobal_dual_smul_cancel (f : X ⟶ Y) (M : Y.Modules)
    (c : Γ(moduleSheafDual M, ⊤)) (x : Γ(M, ⊤))
    (hc : IsRegular (f.appTop (moduleDualEval M ⊤ c x)))
    {r t : Γ(X, ⊤)}
    (h : r • pullGlobal f (moduleSheafDual M) c =
      t • pullGlobal f (moduleSheafDual M) c) : r = t := by
  let E : Γ((pullback f).obj (moduleSheafDual M), ⊤) →ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
    ((moduleDualPullbackPairing f M).val.app (op ⊤)).hom.comp
      (((ModuleSheafTensor.pairing _ _).app ⊤).flip (pullGlobal f M x))
  have he : E (pullGlobal f (moduleSheafDual M) c) =
      f.appTop (moduleDualEval M ⊤ c x) :=
    moduleDualPullbackPairing_unit f M ⊤ c x
  have hh := congrArg E h
  rw [E.map_smul, E.map_smul, he] at hh
  exact hc.right hh
/-- Transport scalar cancellation through a chart comparison. -/
lemma pullGlobal_chart_smul_cancel (f : X ⟶ Y) (j : Y ⟶ Z) (M : Z.Modules)
    (N : Y.Modules) (e : (pullback j).obj M ≅ moduleSheafDual N)
    (c : Γ(M, ⊤)) (d : Γ(moduleSheafDual N, ⊤))
    (he : e.hom.app ⊤ (pullGlobal j M c) = d) (x : Γ(N, ⊤))
    (hc : IsRegular (f.appTop (moduleDualEval N ⊤ d x))) :
    Function.Injective (fun r : Γ(X, ⊤) ↦ r • pullGlobal (f ≫ j) M c) := by
  intro r t h
  apply pullGlobal_dual_smul_cancel f N d x hc
  have h' := congrArg (fun z ↦ ((pullback f).map e.hom).app ⊤
    (((pullbackComp f j).inv.app M).app ⊤ z)) h
  simpa only [Hom.app_smul, pullGlobal_comp, pullGlobal_naturality, he] using h'

/-- A cancellable common section determines the transition on all sections. -/
lemma pullGlobal_coordinate_transition {W : Scheme.{u}}
    (f : X ⟶ Y) (j : Y ⟶ Z) (g : X ⟶ W) (k : W ⟶ Z)
    (h : f ≫ j = g ≫ k) (M : Z.Modules)
    (e : Γ((pullback j).obj M, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤))
    (e' : Γ((pullback k).obj M, ⊤) ≃ₗ[Γ(W, ⊤)] Γ(W, ⊤))
    (c s : Γ(M, ⊤)) (v : Γ(X, ⊤))
    (hc : Function.Injective (fun r : Γ(X, ⊤) ↦ r • pullGlobal (f ≫ j) M c))
    (hv : g.appTop (e' (pullGlobal k M c)) = v * f.appTop (e (pullGlobal j M c))) :
    g.appTop (e' (pullGlobal k M s)) = v * f.appTop (e (pullGlobal j M s)) := by
  have hl := pullGlobal_coordinate_relation f j M e c s
  have hr := pullGlobal_coordinate_relation g k M e' c s
  rw [← h] at hr
  apply hc
  calc
    _ = g.appTop (e' (pullGlobal k M c)) • pullGlobal (f ≫ j) M s := hr.symm
    _ = v • (f.appTop (e (pullGlobal j M c)) • pullGlobal (f ≫ j) M s) := by
      rw [hv, mul_smul]
    _ = v • (f.appTop (e (pullGlobal j M s)) • pullGlobal (f ≫ j) M c) := by rw [hl]
    _ = _ := (mul_smul _ _ _).symm
/-- Flat maps between affine schemes preserve regular global functions. -/
lemma regular_appTop_of_flat (f : X ⟶ Y) [Flat f] [IsAffine X] [IsAffine Y]
    (r : Γ(Y, ⊤)) (hr : IsRegular r) : IsRegular (f.appTop r) := by
  have hf : f.appTop.hom.Flat := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.appLE] using
      Scheme.Hom.flat_appLE f (isAffineOpen_top Y) (isAffineOpen_top X) (by simp)
  let := f.appTop.hom.toAlgebra
  let : Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := hf
  rw [← isLeftRegular_iff_isRegular]
  simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    using (Module.Flat.isSMulRegular_of_isRegular (M := Γ(X, ⊤)) hr)

/-- A canonical Cartier section cancels scalars after flat affine pullback. -/
lemma pullGlobal_divisor_smul_cancel (f : X ⟶ Y) [Flat f] [IsAffine X] [IsAffine Y]
    {I : Y.IdealSheafData} (hI : EffectiveCartier I)
    (hU : CartierChart I ⟨⊤, isAffineOpen_top Y⟩) :
    Function.Injective (fun r : Γ(X, ⊤) ↦
      r • pullGlobal f (divisorLineBundle I hI) (divisorSection hI ⊤)) := by
  have he : moduleDualEval (idealModule I) ⊤ (divisorSection hI ⊤)
      hU.idealSection = hU.choose := by
    change divisorChartEval I ⟨⊤, isAffineOpen_top Y⟩
      (divisorSection hI ⊤) (hU.idealEquiv 1) = _
    rw [divisorSection_eval]
    exact one_mul _
  intro r t h
  apply pullGlobal_dual_smul_cancel f (idealModule I) (divisorSection hI ⊤)
    hU.idealSection _ h
  rw [he]
  exact regular_appTop_of_flat f _ hU.choose_spec.1
end FLT.Mazur.FCurve

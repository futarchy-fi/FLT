/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.RingTheory.Smooth.CotangentBaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Smoothness descends at a chosen prime

Flat base change preserves cotangent homology and differentials. After
localizing at a chosen prime, the resulting map of local rings is faithfully
flat, so formal smoothness descends there without assuming the whole tensor
algebra smooth.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false

open TensorProduct

namespace Algebra

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

attribute [local instance] TensorProduct.rightAlgebra in
/-- For a finitely presented algebra, smoothness at a chosen prime descends
under an arbitrary flat base change. -/
theorem IsSmoothAt.of_flat_tensorProduct [FinitePresentation R S] [Module.Flat R T]
    (q : Ideal (T ⊗[R] S)) [q.IsPrime] [IsSmoothAt T q] :
    IsSmoothAt R (q.comap TensorProduct.includeRight) := by
  let p := q.under S
  let Sp := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap Sp Bq) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p q (algebraMap S (T ⊗[R] S))
      Ideal.LiesOver.over
  have : Module.Flat S (T ⊗[R] S) := by
    let e : T ⊗[R] S ≃ₐ[S] S ⊗[R] T :=
      .ofRingEquiv (f := TensorProduct.comm R T S) (by
        simp [RingHom.algebraMap_toAlgebra])
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  have : Module.FaithfullyFlat Sp Bq := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hΩp : IsBaseChange Sp (KaehlerDifferential.map R R S Sp) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale R S Sp
  have hΩq : IsBaseChange Bq (KaehlerDifferential.map T T (T ⊗[R] S) Bq) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale T (T ⊗[R] S) Bq
  have hΩ := (kaehler_isBaseChange_tensorProduct R S T).comp hΩq
  have eΩ : Bq ⊗[Sp] Ω[Sp⁄R] ≃ₗ[Bq] Ω[Bq⁄T] :=
    AlgebraTensorModule.congr (.refl Bq Bq) hΩp.equiv.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S Sp Bq Bq Ω[S⁄R] ≪≫ₗ hΩ.equiv
  have : Module.FinitePresentation Sp Ω[Sp⁄R] :=
    _root_.FinitePresentation.of_isBaseChange _ hΩp
  have : Module.Flat Bq (Bq ⊗[Sp] Ω[Sp⁄R]) := .of_linearEquiv eΩ
  have : Module.Flat Sp Ω[Sp⁄R] := Module.Flat.of_flat_tensorProduct _ _ Bq
  have hp : IsBaseChange Sp (H1Cotangent.map R R S Sp) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl Sp _).mp inferInstance
  have hq : IsBaseChange Bq (H1Cotangent.map T T (T ⊗[R] S) Bq) :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl Bq _).mp inferInstance
  have h := (H1Cotangent.isBaseChange_tensorProduct R S T).comp hq
  have e : Bq ⊗[Sp] H1Cotangent R Sp ≃ₗ[Bq] H1Cotangent T Bq :=
    AlgebraTensorModule.congr (.refl Bq Bq) hp.equiv.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S Sp Bq Bq (H1Cotangent R S) ≪≫ₗ h.equiv
  have : Subsingleton (Bq ⊗[Sp] H1Cotangent R Sp) := e.subsingleton
  have : Subsingleton (H1Cotangent R Sp) :=
    Module.FaithfullyFlat.lTensor_reflects_triviality Sp Bq _
  exact (formallySmooth_iff R Sp).mpr
    ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

attribute [local instance] TensorProduct.rightAlgebra in
/-- Smoothness at a prime ascends to a prime of a flat tensor base change. -/
theorem IsSmoothAt.flat_tensorProduct [Module.Flat R T]
    (q : Ideal (T ⊗[R] S)) [q.IsPrime]
    [IsSmoothAt R (q.comap TensorProduct.includeRight)] : IsSmoothAt T q := by
  let p := q.under S
  let Sp := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hΩp : IsBaseChange Sp (KaehlerDifferential.map R R S Sp) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale R S Sp
  have hΩq : IsBaseChange Bq (KaehlerDifferential.map T T (T ⊗[R] S) Bq) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale T (T ⊗[R] S) Bq
  have hΩ := (kaehler_isBaseChange_tensorProduct R S T).comp hΩq
  have eΩ : Bq ⊗[Sp] Ω[Sp⁄R] ≃ₗ[Bq] Ω[Bq⁄T] :=
    AlgebraTensorModule.congr (.refl Bq Bq) hΩp.equiv.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S Sp Bq Bq Ω[S⁄R] ≪≫ₗ hΩ.equiv
  have hp : IsBaseChange Sp (H1Cotangent.map R R S Sp) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl Sp _).mp inferInstance
  have hq : IsBaseChange Bq (H1Cotangent.map T T (T ⊗[R] S) Bq) :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl Bq _).mp inferInstance
  have h := (H1Cotangent.isBaseChange_tensorProduct R S T).comp hq
  have e : Bq ⊗[Sp] H1Cotangent R Sp ≃ₗ[Bq] H1Cotangent T Bq :=
    AlgebraTensorModule.congr (.refl Bq Bq) hp.equiv.symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange S Sp Bq Bq (H1Cotangent R S) ≪≫ₗ h.equiv
  have hs : FormallySmooth R Sp := ‹IsSmoothAt R (q.comap TensorProduct.includeRight)›
  have : Module.Projective Sp Ω[Sp⁄R] := (formallySmooth_iff R Sp).mp hs |>.1
  have : Subsingleton (H1Cotangent R Sp) := (formallySmooth_iff R Sp).mp hs |>.2
  have : Module.Projective Bq Ω[Bq⁄T] := .of_equiv eΩ
  have : Subsingleton (H1Cotangent T Bq) := e.symm.subsingleton
  exact (formallySmooth_iff T Bq).mpr ⟨inferInstance, inferInstance⟩

/-- In particular, smoothness at a chosen point descends under any field extension. -/
theorem IsSmoothAt.of_fieldExtension {K L A : Type*} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A] [FinitePresentation K A]
    (q : Ideal (L ⊗[K] A)) [q.IsPrime] [IsSmoothAt L q] :
    IsSmoothAt K (q.comap TensorProduct.includeRight) :=
  .of_flat_tensorProduct q

end Algebra

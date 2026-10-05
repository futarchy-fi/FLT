/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralClosedImmersion
public import FLT.GroupScheme.EtaleModelIdentification
public import FLT.GroupScheme.RaynaudModelUpperBound

/-! # Generic injections into finite étale models are closed immersions -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  {X Y : FF R K}

/-- A generic isomorphism to an étale model is surjective on integral coordinates. -/
theorem ModelHom.surjective_of_etale_target (f : ModelHom X Y)
    [Algebra.Etale R Y.CoordinateRing] (hf : Function.Bijective (genericHom f)) :
    Function.Surjective f := by
  obtain ⟨g, hg, _⟩ := extend_generic_morphism_of_etale Y X ((genericHom f).inverse hf)
  have he : f.comp g = BialgHom.id R X.CoordinateRing := by
    apply genericHom_injective
    ext x
    simp only [genericHom_comp, hg, GenericGaloisHom.inverse_apply, genericHom_id]
  exact fun x ↦ ⟨g x, DFunLike.congr_fun he x⟩

/-- A generic injection into a finite étale target is already integrally closed. -/
theorem ModelHom.closed_of_etale_target (f : ModelHom X Y)
    [Algebra.Etale R Y.CoordinateRing] (hf : Function.Injective (genericHom f)) :
    Function.Surjective f := by
  let C := (genericHom f).closure hf
  let : Algebra.FormallyUnramified R C.CoordinateRing :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R _)
      Ideal.Quotient.mk_surjective
  let : Algebra.FinitePresentation R C.CoordinateRing :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale R C.CoordinateRing :=
    Algebra.Etale.of_formallyUnramified_of_flat
  have hc : Function.Bijective (genericHom (f.closureComparison hf)) := by
    constructor
    · intro x y h
      simpa only [ModelHom.closureComparisonPoints] using h
    · exact fun x ↦ ⟨x, f.closureComparisonPoints hf x⟩
  have hs := (f.closureComparison hf).surjective_of_etale_target hc
  intro x
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨b, DFunLike.congr_fun (f.closureComparisonInclusion hf) b⟩
end ThreeAdicPlan

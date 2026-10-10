/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassInfinitesimalGroupPoints

/-!
# Every infinitesimal identity point lies in the constructed chart

A square-zero quotient is surjective on spectra. A point reducing to the
identity therefore lies entirely in the original Y chart. Recovering its
algebra map identifies it with one of the previously constructed parameters.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R)

/-- Recover an algebra map from any relative chart morphism, without a field hypothesis. -/
def relativeChartAlgHom (j : Fin 3) (f : Spec (.of A) ⟶ chartScheme W j)
    (hf : f ≫ chartStructure W j = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Coordinate W j →ₐ[R] A := by
  refine { (Spec.preimage f).hom with commutes' := ?_ }
  intro r
  have he : Spec.map (CommRingCat.ofHom
      ((Spec.preimage f).hom.comp (algebraMap R (Coordinate W j)))) =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [show CommRingCat.ofHom ((Spec.preimage f).hom.comp
      (algebraMap R (Coordinate W j))) =
        CommRingCat.ofHom (algebraMap R (Coordinate W j)) ≫ Spec.preimage f from rfl,
      Spec.map_comp, Spec.map_preimage]
    exact hf
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective he)) r

/-- Recovering the algebra map retains the entire original chart morphism. -/
theorem relativeChartAlgHom_spec (j : Fin 3) (f : Spec (.of A) ⟶ chartScheme W j)
    (hf : f ≫ chartStructure W j = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec.map (CommRingCat.ofHom (relativeChartAlgHom W j f hf).toRingHom) = f :=
  Spec.map_preimage f

variable (I : Ideal A) (hI : I ^ 2 = ⊥)

include hI

/-- A square-zero quotient has the same underlying points as the original affine scheme. -/
theorem squareZero_quotient_spec_surjective :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  apply (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical (I := I) ?_).2
  intro a ha
  exact (mem_nilradical).mpr ⟨2, by
    simpa only [pow_two] using squareZero_mul I hI ha ha⟩

/-- Every relative point reducing to the identity has an actual infinitesimal chart parameter. -/
theorem exists_infinitesimal_chart_parameter (p : Spec (.of A) ⟶ integralCurve W)
    (hp : p ≫ integralCurveStructure W = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ p =
      Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := A ⧸ I) W).toRingHom) ≫
        integralCurveChart W 1) :
    ∃ x : I, Spec.map (CommRingCat.ofHom (infinitesimalChartPoint W I hI x).val.toRingHom) ≫
      integralCurveChart W 1 = p := by
  have hr : Set.range p ⊆ Set.range (integralCurveChart W 1) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := squareZero_quotient_spec_surjective I hI a
    exact ⟨_, congrArg (fun f : Spec (.of (A ⧸ I)) ⟶ integralCurve W ↦ f b) hred.symm⟩
  let l := IsOpenImmersion.lift (integralCurveChart W 1) p hr
  have hl : l ≫ integralCurveChart W 1 = p := IsOpenImmersion.lift_fac _ _ _
  have hb : l ≫ chartStructure W 1 = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← integralCurveChart_structure, ← Category.assoc, hl, hp]
  let F := relativeChartAlgHom W 1 l hb
  have hF : Spec.map (CommRingCat.ofHom F.toRingHom) = l := relativeChartAlgHom_spec W 1 l hb
  have he : Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mkₐ R I).comp F).toRingHom) =
      Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := A ⧸ I) W).toRingHom) := by
    apply (cancel_mono (integralCurveChart W 1)).mp
    change Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp F.toRingHom)) ≫ _ = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hF, Category.assoc, hl]
    exact hred
  have hC : (Ideal.Quotient.mkₐ R I).comp F = chartInfinityEvaluation W := by
    apply AlgHom.ext
    intro a
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective he)) a
  let q : InfinitesimalChart W I := ⟨F, (infinitesimalChart_iff_reduction W I F).mpr hC⟩
  obtain ⟨x, hx⟩ := (infinitesimalChartEquiv W I hI).surjective q
  refine ⟨x, ?_⟩
  have hx' : (infinitesimalChartPoint W I hI x).val = F := congrArg Subtype.val hx
  rw [hx', hF, hl]

end FLT.Mazur.WeierstrassIntegralChart

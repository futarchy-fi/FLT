/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationTensorCharts
public import FLT.Mazur.PrincipalLocalizationSquare

/-!
# Literal principal-localization models for original relation neighborhoods

The constructed whole-fiber neighborhoods are spectra of principal
localizations of the actual tensor envelope. The isomorphism preserves the
original inclusion into that envelope; no affine quotient is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
local notation "Y" => Over.left (prod A V)
/-- The original structural algebra on source coefficients. -/
local instance principalSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The original structural algebra on translation-base coefficients. -/
local instance principalTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom

/-- The original affine product as the spectrum of its actual tensor coefficients. -/
def tensorSpectrumMap : Y ⟶ Spec (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤))) :=
  let _ := variableHilbertOverlap_envelope_affine V A
  (Y).isoSpec.hom ≫ Spec.map (tensorIso A V).hom

instance tensorSpectrumMap_isIso : IsIso (tensorSpectrumMap V (A := A)) := by
  let _ := variableHilbertOverlap_envelope_affine V A
  dsimp only [tensorSpectrumMap]
  infer_instance

omit [Algebra.FiniteType ℤ R] in
/-- The tensor element cuts out exactly the original envelope principal open. -/
theorem tensorSpectrumMap_preimage (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) :
    tensorSpectrumMap V (A := A) ⁻¹ᵁ PrimeSpectrum.basicOpen t =
      (Y).basicOpen ((tensorIso A V).hom t) := by
  change (Y).toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen ((tensorIso A V).hom t) = _
  exact Scheme.toSpecΓ_preimage_basicOpen _ _

variable [IsOpenImmersion k.left]
  (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) (U : (relation f hL d V c k).left.Opens)

/-- The original chart inclusion has precisely the intended principal tensor-spectrum image. -/
theorem principalTensor_range
    (hU : (j) ''ᵁ U = (Y).basicOpen ((tensorIso A V).hom t)) :
    (U.ι ≫ j ≫ tensorSpectrumMap V).opensRange = PrimeSpectrum.basicOpen t := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, Scheme.Hom.comp_image,
    hU, ← tensorSpectrumMap_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.opensRange_of_isIso]
  exact inf_eq_right.mpr le_top

/-- The actual relation neighborhood is the spectrum of a literal tensor localization. -/
def principalTensorIso
    (hU : (j) ''ᵁ U = (Y).basicOpen ((tensorIso A V).hom t)) :
    U.toScheme ≅ Spec (.of (Localization.Away t)) :=
  IsOpenImmersion.isoOfRangeEq (U.ι ≫ j ≫ tensorSpectrumMap V)
    (PrincipalLocalizationSquare.inclusion t) (by
      have h := (principalTensor_range f hL d V c k t U hU).trans
        (PrincipalLocalizationSquare.inclusion_opensRange t).symm
      exact congrArg (fun W : (Spec (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))).Opens ↦
        (W : Set (Spec (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))))) h)

/-- The localization model retains the actual inclusion and both tensor coefficients. -/
@[reassoc]
theorem principalTensorIso_inclusion
    (hU : (j) ''ᵁ U = (Y).basicOpen ((tensorIso A V).hom t)) :
    (principalTensorIso f hL d V c k t U hU).hom ≫
      PrincipalLocalizationSquare.inclusion t = U.ι ≫ j ≫ tensorSpectrumMap V :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The constructed literal localization model contains both complete original endpoint fibers. -/
theorem exists_endpoint_fibers_tensor_model [Etale V.hom] (x : A.left)
    (W : (relation f hL d V c k).left.Opens)
    (hW : (fst f hL d V c k).left ⁻¹' {x} ∪ (snd f hL d V c k).left ⁻¹' {x} ⊆ W) :
    ∃ (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤))
      (U : (relation f hL d V c k).left.Opens),
      IsAffineOpen U ∧
        (fst f hL d V c k).left ⁻¹' {x} ∪ (snd f hL d V c k).left ⁻¹' {x} ⊆ U ∧ U ≤ W ∧
        ∃ e : U.toScheme ≅ Spec (.of (Localization.Away t)),
          e.hom ≫ PrincipalLocalizationSquare.inclusion t = U.ι ≫ j ≫ tensorSpectrumMap V := by
  obtain ⟨t, U, ha, hF, hUW, hU⟩ := exists_tensor_principal_chart f hL d V c k x W hW
  exact ⟨t, U, ha, hF, hUW, principalTensorIso f hL d V c k t U hU,
    principalTensorIso_inclusion f hL d V c k t U hU⟩

end FLT.Mazur.HilbertChart.AffineRestriction

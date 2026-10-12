/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertLocalizedCoefficients

/-!
# Literal tensor formulas for the actual local endpoint maps

The coefficient comparison identifies restriction of envelope coefficients
with the literal localization map. In particular the second endpoint is the
localized first tensor factor; the first endpoint remains the constructed
translation map into this same localized ring.
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
  [IsOpenImmersion k.left]
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)
/-- The algebra induced by the original source structural morphism. -/
local instance formulaSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance formulaTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤))
  (U : (relation f hL d V c k).left.Opens)
  (hU : (toEnvelope f hL d V c k).left ''ᵁ U =
    (prod A V).left.basicOpen ((tensorIso A V).hom t))

omit [Algebra.FiniteType ℤ R] [IsOpenImmersion k.left] in
/-- The tensor spectrum map pulls a canonical tensor section back to its envelope coefficient. -/
theorem tensorSpectrumMap_section (z : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) :
    (tensorSpectrumMap V (A := A)).appTop
      ((Scheme.ΓSpecIso (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))).inv z) =
      (tensorIso A V).hom z := by
  let _ := variableHilbertOverlap_envelope_affine V A
  simpa only [tensorSpectrumMap, Scheme.Hom.comp_appTop, Scheme.isoSpec_hom,
    Scheme.toSpecΓ_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply] using
    congrArg (fun g ↦ g ((Scheme.ΓSpecIso
      (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))).inv z))
      (Scheme.ΓSpecIso_naturality (tensorIso A V).hom)

attribute [local irreducible] principalTensorIso tensorSpectrumMap

/-- Restricting the actual tensor envelope is exactly the literal localization ring map. -/
theorem principalTensorSectionsIso_tensor (z : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) :
    (principalTensorSectionsIso f hL d V c k t U hU).hom
      (U.ι.appTop (tensorCoordinates f hL d V c k z)) =
        algebraMap _ (Localization.Away t) z := by
  let e := principalTensorIso f hL d V c k t U hU
  have he : e.inv ≫ U.ι ≫ j ≫ tensorSpectrumMap V =
      PrincipalLocalizationSquare.inclusion t := by
    rw [← principalTensorIso_inclusion f hL d V c k t U hU]
    exact e.inv_hom_id_assoc _
  have hz := congrArg (fun g ↦ (Scheme.ΓSpecIso (.of (Localization.Away t))).hom
    (g.appTop ((Scheme.ΓSpecIso
      (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))).inv z))) he
  have hn := congrArg (fun g ↦ g ((Scheme.ΓSpecIso
    (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))).inv z))
      (Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (algebraMap _ (Localization.Away t))))
  change (Scheme.ΓSpecIso (.of (Localization.Away t))).hom
    ((PrincipalLocalizationSquare.inclusion t).appTop
      ((Scheme.ΓSpecIso (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))).inv z)) =
        algebraMap _ (Localization.Away t) ((Scheme.ΓSpecIso
          (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))).hom
            ((Scheme.ΓSpecIso (.of (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)))).inv z)) at hn
  rw [Iso.inv_hom_id_apply] at hn
  change (Scheme.ΓSpecIso (.of (Localization.Away t))).hom
    (e.inv.appTop (U.ι.appTop ((j).appTop _))) = _ at hz
  have hs := congrArg (fun w : Γ((prod A V).left, ⊤) ↦
    (Scheme.ΓSpecIso (.of (Localization.Away t))).hom
      (e.inv.appTop (U.ι.appTop ((j).appTop w))))
    (tensorSpectrumMap_section V (A := A) z)
  exact hs.symm.trans (hz.trans hn)

/-- The actual test endpoint is the literal first tensor factor followed by localization. -/
theorem localizedTestMap_eq_localization (a : Γ(A.left, ⊤)) :
    localizedTestMap f hL d V c k t U hU a =
      algebraMap _ (Localization.Away t) (a ⊗ₜ[R] (1 : Γ(V.left, ⊤))) := by
  rw [← principalTensorSectionsIso_tensor f hL d V c k t U hU]
  change _ = (principalTensorSectionsIso f hL d V c k t U hU).hom
    (U.ι.appTop (tensorCoordinates f hL d V c k (a ⊗ₜ[R] 1)))
  rw [tensorCoordinates_tmul, map_one, mul_one]
  rfl

/-- The literal localized source map respects the original R-algebra structures. -/
def localizedSourceAlgHom : Γ(A.left, ⊤) →ₐ[R] Localization.Away t := by
  refine ⟨localizedSourceMap f hL d V c k t U hU, ?_⟩
  intro r
  change localizedSourceMap f hL d V c k t U hU (algebraMap R Γ(A.left, ⊤) r) = _
  rw [localizedSourceMap_scalar, localizedTestMap_eq_localization,
    ← Algebra.TensorProduct.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply R (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤))]

/-- The literal localized test map is the other original R-algebra morphism. -/
def localizedTestAlgHom : Γ(A.left, ⊤) →ₐ[R] Localization.Away t := by
  refine ⟨localizedTestMap f hL d V c k t U hU, ?_⟩
  intro r
  change localizedTestMap f hL d V c k t U hU (algebraMap R Γ(A.left, ⊤) r) = _
  rw [localizedTestMap_eq_localization, ← Algebra.TensorProduct.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply R (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤))]

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessAffineCoherence
public import FLT.Mazur.CoherentOpenDescent
public import FLT.Mazur.ChowAffineBaseSectionsAssembly

/-!
# Affine coherence of Chow witnesses

Localization identifies the actual direct image on each affine spectrum with
its canonical tilde. Projective degree-zero finiteness supplies finite sections.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve CoherentDevissage

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat} [IsNoetherianRing R] {X : Scheme} (f : X ⟶ Spec R)
  [IsProper f]

set_option maxHeartbeats 800000 in
-- Comparing restriction maps unfolds both affine section equivalences.
/-- Localization of the actual restriction makes the canonical affine counit invertible. -/
theorem graphPowerAffine_fromTildeΓ_isIso (n : ℕ) (V : X.affineOpens) :
    IsIso ((graphPowerPushforward f n).restrict V.2.fromSpec).fromTildeΓ := by
  apply (isIso_fromTildeΓ_iff_isLocalizing _).mpr
  intro r
  let M := graphPowerPushforward f n
  let N := M.restrict V.2.fromSpec
  let a := affineTopSectionsEquiv M V
  let b := affineImageSectionsEquiv M V (PrimeSpectrum.basicOpen r)
    (X.basicOpen r) (X.basicOpen_le r) (V.2.fromSpec_image_basicOpen r)
  let p := ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  have hsquare : b.toLinearMap.comp p =
      (graphPowerRestriction f n V.1 r).comp a.toLinearMap := by
    ext s
    change M.presheaf.map _ (N.presheaf.map _ s) =
      M.presheaf.map _ (M.presheaf.map _ s)
    simp only [N, restrict_map]
    erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    rfl
  apply (IsLocalizedModule.comp_iff_of_bijective_left (.powers r) b.toLinearMap b.bijective).mp
  rw [hsquare]
  let := graphPowerRestriction_isLocalized f n V.1 V.2 r
  exact IsLocalizedModule.of_linearEquiv_right (.powers r)
    (graphPowerRestriction f n V.1 r) a

/-- The canonical tilde comparison on the spectrum of an affine target open. -/
def graphPowerAffineIso (n : ℕ) (V : X.affineOpens) :
    (graphPowerPushforward f n).restrict V.2.fromSpec ≅
      tilde (moduleSpecΓFunctor.obj ((graphPowerPushforward f n).restrict V.2.fromSpec)) := by
  letI := graphPowerAffine_fromTildeΓ_isIso f n V
  exact (asIso ((graphPowerPushforward f n).restrict V.2.fromSpec).fromTildeΓ).symm

open FLT.Mazur.ProjectiveSpace LocalizationDegree

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Global sections upstairs are the actual direct-image sections on the target open. -/
def graphPowerSectionsEquiv (n : ℕ) (V : X.affineOpens) :
    baseSections (graphPowerOver f n V.1) (graphPowerBaseScalars f V.1 V.2) ⊤ ≃ₗ[Γ(X, V.1)]
      Γ(graphPowerPushforward f n, V.1) := by
  have ht : (graphClosureπ f ∣_ V.1) ⁻¹ᵁ V.1.ι ⁻¹ᵁ V.1 = ⊤ := by simp
  let a : baseSections (graphPowerOver f n V.1) (graphPowerBaseScalars f V.1 V.2) ⊤ ≃ₗ[Γ(X, V.1)]
      baseSections (graphPowerOver f n V.1) (graphPowerBaseScalars f V.1 V.2)
        ((graphClosureπ f ∣_ V.1) ⁻¹ᵁ V.1.ι ⁻¹ᵁ V.1) := by
    rw [ht]
  exact a.trans ((graphOriginalBaseEquiv f n V.1 V.2 V.1 le_rfl).trans
    (ModuleCat.restrictScalarsId'App (R := Γ(X, V.1)) _ (by
      change (X.presheaf.map (𝟙 (op V.1))).hom = RingHom.id _
      rw [X.presheaf.map_id]; rfl)
      ((graphPowerPushforward f n).val.obj (op V.1))).toLinearEquiv)

/-- Projective degree-zero finiteness applies with the actual affine-base scalar action. -/
theorem graphPowerOver_sections_finite (n : ℕ) (V : X.affineOpens) :
    Module.Finite Γ(X, V.1)
      (baseSections (graphPowerOver f n V.1) (graphPowerBaseScalars f V.1 V.2) ⊤) := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := IsLocallyNoetherian.component_noetherian V
  let := graphLineBundlePower_isFinitePresentation f n
  let := coherent_restrict (graphClosureπ f ⁻¹ᵁ V.1).ι (graphLineBundlePower f n)
  let P := graphLineBundleAffinePresentation f V.1 V.2
  let ρ := graphPowerBaseScalars f V.1 V.2
  have hρ : P.embedding.appTop.hom.comp
      (constantSection Γ(X, V.1) (Fin (P.dimension + 1)) ⊤) = ρ := by
    rw [← projectiveBaseScalars_eq]
    change ((Scheme.ΓSpecIso Γ(X, V.1)).inv ≫
      (baseProjection Γ(X, V.1) _).appTop ≫ P.embedding.appTop).hom = _
    rw [← Scheme.Hom.comp_appTop, P.over]
    rfl
  have hfinite := closedSubscheme_coherent_moduleH_finite Γ(X, V.1)
    (Fin (P.dimension + 1)) P.embedding (graphPowerOver f n V.1) 0
  rw [hρ] at hfinite
  let := Module.compHom (ModuleH (graphPowerOver f n V.1) 0) ρ
  let := hfinite
  let e : ModuleH (graphPowerOver f n V.1) 0 ≃ₗ[Γ(X, V.1)]
      baseSections (graphPowerOver f n V.1) ρ ⊤ :=
    { (moduleH0Equiv (graphPowerOver f n V.1)).toAddEquiv with
      map_smul' := fun r s ↦ by
        change moduleH0Equiv _ (ρ r • s) =
          ((graphClosureπ f ⁻¹ᵁ V.1).toScheme.presheaf.map (𝟙 (op ⊤))) (ρ r) • _
        rw [(graphClosureπ f ⁻¹ᵁ V.1).toScheme.presheaf.map_id]
        exact (moduleH0Equiv _).map_smul (ρ r) s }
  exact Module.Finite.equiv e

/-- The affine spectrum chart has finite global sections, by its projective presentation. -/
theorem graphPowerAffine_sections_finite (n : ℕ) (V : X.affineOpens) :
    Module.Finite Γ(X, V.1) Γ((graphPowerPushforward f n).restrict V.2.fromSpec, ⊤) := by
  let := graphPowerOver_sections_finite f n V
  exact Module.Finite.equiv ((graphPowerSectionsEquiv f n V).trans
    (affineTopSectionsEquiv (graphPowerPushforward f n) V).symm)

/-- Finite sections and the localization comparison give coherence on the affine spectrum. -/
theorem graphPowerAffine_isFinitePresentation (n : ℕ) (V : X.affineOpens) :
    ((graphPowerPushforward f n).restrict V.2.fromSpec).IsFinitePresentation := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := IsLocallyNoetherian.component_noetherian V
  let := (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
    (graphPowerAffine_fromTildeΓ_isIso f n V)
  exact (affineCoherent_iff_finite_sections _).mpr (graphPowerAffine_sections_finite f n V)

/-- The actual two-stage restriction has its canonical tilde comparison. -/
def graphPowerAffineRestrictionIso (n : ℕ) (V : X.affineOpens) :
    ((graphPowerPushforward f n).restrict V.1.ι).restrict V.2.isoSpec.inv ≅
      tilde (moduleSpecΓFunctor.obj
        (((graphPowerPushforward f n).restrict V.1.ι).restrict V.2.isoSpec.inv)) := by
  let e := (restrictFunctorComp V.2.isoSpec.inv V.1.ι).app (graphPowerPushforward f n)
  letI : (((graphPowerPushforward f n).restrict V.1.ι).restrict
      V.2.isoSpec.inv).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation _).prop_of_iso e
      (graphPowerAffine_isFinitePresentation f n V)
  exact affineCoherentIso _

/-- Coherence on the spectrum transports back to the prescribed affine open. -/
theorem graphPowerAffineRestriction_isFinitePresentation (n : ℕ) (V : X.affineOpens) :
    ((graphPowerPushforward f n).restrict V.1.ι).IsFinitePresentation := by
  let M := graphPowerPushforward f n
  let := graphPowerAffine_isFinitePresentation f n V
  let e : (M.restrict V.2.fromSpec).restrict V.2.isoSpec.hom ≅ M.restrict V.1.ι :=
    (restrictFunctorComp V.2.isoSpec.hom V.2.fromSpec).symm.app M ≪≫
      (restrictFunctorCongr V.2.isoSpec_hom_fromSpec).app M
  exact (SheafOfModules.isFinitePresentation _).prop_of_iso e
    (coherent_restrict V.2.isoSpec.hom (M.restrict V.2.fromSpec))

/-- Coherence of the actual direct image follows from its affine restrictions. -/
theorem chowPushforwardPower_isFinitePresentation (n : ℕ) :
    (graphPowerPushforward f n).IsFinitePresentation :=
  coherent_of_openCover (graphPowerPushforward f n)
    (fun V : X.affineOpens ↦ V.1) (iSup_affineOpens_eq_top X)
    (graphPowerAffineRestriction_isFinitePresentation f n)

end FLT.Mazur.Chow.AffineBase

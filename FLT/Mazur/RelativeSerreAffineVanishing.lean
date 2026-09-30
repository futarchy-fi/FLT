/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedProjectiveSerreVanishing
public import FLT.Mazur.RelativeSerreLocalizedTower

/-!
# A uniform Serre bound on all principal affine-base opens

One coherent presentation tower is chosen over the original base. Its maximum
degree works on every principal localization. The line coefficient data consist
only of actual isomorphisms with the localized projective twists, including the
zeroth power; no vanishing or resolution is an input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Dimension shifting on an explicit tower uses only its maximum presentation degree. -/
theorem ExactTwistTower.moduleH_subsingleton {R : Type} [CommRing R]
    {ι : Type} [Fintype ι] {F : (space R ι).Modules}
    {c : ℕ} (T : ExactTwistTower R ι F c) [hF : F.IsFinitePresentation]
    (n : ℕ) (hn : T.bound ≤ n) (q : ℕ) (hq : Fintype.card ι ≤ q + 1 + c) :
    Subsingleton (ModuleH (twistTensor R ι F (n : ℤ)) (q + 1)) := by
  revert hF
  induction T generalizing q with
  | zero F =>
    intro hF
    exact finiteAffineCover_moduleH_subsingleton (twistTensor R ι F (n : ℤ))
      (chart R ι) (fun i ↦ Proj.isAffineOpen_basicOpen (grading R ι) (X i)
        (isHomogeneous_X R i) (by decide)) (iSup_chart R ι) (q + 1) (by omega)
  | @step F c d κ hκ C hC source target tail ih =>
    intro hF
    let := hκ
    let := hC.finite₁
    have hd : d ≤ n := le_trans (le_max_left _ _) hn
    have ht : tail.bound ≤ n := le_trans (le_max_right _ _) hn
    let _kernelZero := ih ht (q + 1) (by omega)
    let _sumZero := twistTensor_twistSum_moduleH_subsingleton R ι
      (κ := κ) (-(d : ℤ)) (n : ℤ) (by omega) q
    let _middleZero : Subsingleton (ModuleH (twistTensor R ι C.X₂ (n : ℤ)) (q + 1)) :=
      @moduleH_subsingleton_of_iso (space R ι) _ _
        ((twistTensorFunctor R ι (n : ℤ)).mapIso source) (q + 1) _sumZero
    let _rightZero := @moduleH_subsingleton_right (space R ι)
      (C.map (twistTensorFunctor R ι (n : ℤ)))
      (twistTensor_shortExact R ι C hC.shortExact (n : ℤ)) (q + 1) _middleZero _kernelZero
    exact @moduleH_subsingleton_of_iso (space R ι) _ _
      ((twistTensorFunctor R ι (n : ℤ)).mapIso target.symm) (q + 1) _rightZero

/-- The affine-local coefficient data supplied by a line's projective presentation. -/
structure AffineLineCoefficients {R : Type} [CommRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) (L : Y.Modules) where
  /-- Each actual restricted tensor power is the pullback of the corresponding local twist. -/
  powerIso : ∀ (n : ℕ) (r : R),
    (ModuleLineBundleTensorPullback.tensorPower L n).restrict (principalSource i r).ι ≅
      (Scheme.Modules.pullback (principalEmbedding i r)).obj (O (Localization.Away r) d (n : ℤ))

/-- A global identification with the pulled-back hyperplane line supplies all local powers. -/
def AffineLineCoefficients.ofIso {R : Type} [CommRing R]
    {Y : Scheme} {d : ℕ} (i : Y ⟶ space R (Fin (d + 1)))
    {L : Y.Modules} (e : L ≅ (Scheme.Modules.pullback i).obj (O R d 1)) :
    AffineLineCoefficients i L where
  powerIso n r := (restrictFunctor (principalSource i r).ι).mapIso
    (lineTensorPowerIso e n ≪≫ (closedTwistPowerIso R (Fin (d + 1)) i n).symm) ≪≫
      principalTwistingIso i r (n : ℤ)

/-- One bound works for every principal open and every positive cohomological degree. -/
theorem exists_principal_line_power_moduleH_subsingleton {R : Type} [CommRing R]
    [IsNoetherianRing R] {Y : Scheme} {d : ℕ}
    (i : Y ⟶ space R (Fin (d + 1))) [IsClosedImmersion i]
    (L : Y.Modules) (D : AffineLineCoefficients i L) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r : R, ∀ q : ℕ,
      Subsingleton (ModuleH
        ((ModuleLineBundleTensorPullback.tensorPower L n).restrict (principalSource i r).ι)
        (q + 1)) := by
  let F := (pushforward i).obj (structureModule Y)
  let : (structureModule Y).IsFinitePresentation := unitSheaf_isFinitePresentation Y
  let : F.IsFinitePresentation := CoherentDevissage.closedPushforward_isFinitePresentation i _
  let T := coherentTwistPresentationTower R (Fin (d + 1)) F (d + 1)
  refine ⟨T.bound, fun n hn r q ↦ ?_⟩
  let ψ := algebraMap R (Localization.Away r)
  let j := principalEmbedding i r
  let F' := F.restrict (coefficientMap ψ (Fin (d + 1)))
  let : F'.IsFinitePresentation := coherent_restrict _ F
  let T' := localizeTower ψ (Fin (d + 1)) T
  have hbound : T'.bound ≤ n := by rwa [localizeTower_bound]
  let _localizedZero := T'.moduleH_subsingleton n hbound q (by simp)
  let eF : F' ≅ (pushforward j).obj (structureModule (principalSource i r).toScheme) :=
    principalClosedCoefficientIso i r (structureModule Y) ≪≫
      (pushforward j).mapIso (restrictUnitIso (principalSource i r).ι)
  let A := O (Localization.Away r) d (n : ℤ)
  have hA : LocallyFreeRankOne A := twistingSheaf_locallyFreeRankOne _ _ _
  let M := ModuleSheafTensor.tensor (structureModule (principalSource i r).toScheme)
    ((Scheme.Modules.pullback j).obj A)
  let : (structureModule (principalSource i r).toScheme).IsFinitePresentation :=
    unitSheaf_isFinitePresentation _
  let : M.IsFinitePresentation := tensor_line_isFinitePresentation _ _ (hA.pullback j)
  let eM : (pushforward j).obj M ≅ twistTensor (Localization.Away r) (Fin (d + 1)) F'
      (n : ℤ) :=
    ClosedLineProjectionFormula.projectionIso j _ A hA ≪≫
      (twistTensorFunctor (Localization.Away r) (Fin (d + 1)) (n : ℤ)).mapIso eF.symm
  let _pushforwardZero := moduleH_subsingleton_of_iso eM (q + 1)
  let _sourceZero : Subsingleton (ModuleH M (q + 1)) :=
    (closedPushforwardModuleHEquiv j M (q + 1)).symm.toEquiv.injective.subsingleton
  exact @moduleH_subsingleton_of_iso (principalSource i r).toScheme _ _
    (D.powerIso n r ≪≫ (ModuleSheafTensor.leftUnitor _).symm) (q + 1) _sourceZero

/-- The uniform conclusion for a specified affine-base map and its projective presentation. -/
theorem exists_affine_line_power_moduleH_subsingleton {R : Type} [CommRing R]
    [IsNoetherianRing R] {Y : Scheme} {d : ℕ} (π : Y ⟶ Spec (.of R))
    (i : Y ⟶ space R (Fin (d + 1))) [IsClosedImmersion i]
    (hπ : i ≫ baseProjection R _ = π) (L : Y.Modules) (D : AffineLineCoefficients i L) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r : R, ∀ q : ℕ,
      Subsingleton (ModuleH ((ModuleLineBundleTensorPullback.tensorPower L n).restrict
        (π ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι) (q + 1)) := by
  subst π
  exact exists_principal_line_power_moduleH_subsingleton i L D

end FLT.Mazur.ProjectiveSpace

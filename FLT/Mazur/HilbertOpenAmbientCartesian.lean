/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientBaseChange
public import FLT.Mazur.IdealFamilyIsomorphism
public import FLT.Mazur.RelativeIdealFamilies

/-!
# Identifying the relative ambient open with its actual scheme pullback

The inverse-image open used by Hilbert classification is canonically the
base change of the original open scheme. This identifies the represented
ideal families with the intrinsic full ideals on that actual scheme pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- The original ambient open as an actual scheme over the coefficient scheme. -/
def quotientOriginalOpenStructure : U.toScheme ⟶ Spec (.of R) :=
  U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K)))

/-- The relative ambient open maps to the original ambient open by restriction. -/
def quotientRelativeOpenOriginalMap : (quotientRelativeOpen R I K U s).toScheme ⟶ U.toScheme :=
  (pullback.snd s
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K))))) ∣_ U

/-- The original-open projection retains the actual containing-ambient projection. -/
@[reassoc]
theorem quotientRelativeOpenOriginalMap_ι :
    quotientRelativeOpenOriginalMap R I K U s ≫ U.ι =
      (quotientRelativeOpen R I K U s).ι ≫ pullback.snd _ _ := morphismRestrict_ι _ _

/-- The relative ambient open is itself the actual base change of the original open. -/
theorem quotientRelativeOpenOriginalMap_isPullback :
    IsPullback (quotientRelativeOpenOriginalMap R I K U s)
      ((quotientRelativeOpen R I K U s).ι ≫ pullback.fst _ _)
      (quotientOriginalOpenStructure R I K U) s :=
  (isPullback_morphismRestrict (pullback.snd s
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K))))) U).paste_vert
      (IsPullback.of_hasPullback _ _).flip

/-- The canonical actual-scheme comparison with the base change of the original ambient open. -/
def quotientRelativeOpenIso :
    (quotientRelativeOpen R I K U s).toScheme ≅
      pullback s (quotientOriginalOpenStructure R I K U) :=
  (quotientRelativeOpenOriginalMap_isPullback R I K U s).flip.isoPullback

/-- The canonical comparison preserves the actual family base projection. -/
@[reassoc]
theorem quotientRelativeOpenIso_hom_fst :
    (quotientRelativeOpenIso R I K U s).hom ≫ pullback.fst _ _ =
      (quotientRelativeOpen R I K U s).ι ≫ pullback.fst _ _ :=
  (quotientRelativeOpenOriginalMap_isPullback R I K U s).flip.isoPullback_hom_fst

/-- The canonical comparison preserves the original open ambient projection. -/
@[reassoc]
theorem quotientRelativeOpenIso_hom_snd :
    (quotientRelativeOpenIso R I K U s).hom ≫ pullback.snd _ _ =
      quotientRelativeOpenOriginalMap R I K U s :=
  (quotientRelativeOpenOriginalMap_isPullback R I K U s).flip.isoPullback_hom_snd

/-- Full relative-open ideals are exactly intrinsic families in the original-open pullback. -/
def openQuotientIntrinsicFamilyEquiv (d : ℕ) :
    OpenQuotientSchemeFamilies R I d K U s ≃
      RelativeIdealFamilies (quotientOriginalOpenStructure R I K U) d s :=
  idealFamilyIsoEquiv (quotientRelativeOpenIso R I K U s) _ _
    (quotientRelativeOpenIso_hom_fst R I K U s) d

end FLT.Mazur.HilbertChart

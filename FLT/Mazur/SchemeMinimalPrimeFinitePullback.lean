/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Whole-source finiteness over original minimal-prime localizations

A Noetherian ring localized at an original minimal prime is Artinian, including
its nilpotents. Every quasi-compact quasi-finite source becomes finite over
this actual localization. Neither a reduced component nor a residue field is
substituted for it. Spreading this finiteness to an original open is separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeMinimalPrimeFinitePullback
variable {R : Type} [CommRing R] [IsNoetherianRing R]
  (P : PrimeSpectrum R)

/-- The unchanged minimal-prime localization retains its full Artinian coefficient ring. -/
theorem localization_isArtinian (hP : P.asIdeal ∈ minimalPrimes R) :
    IsArtinianRing (Localization.AtPrime P.asIdeal) := by
  apply isArtinianRing_iff_krullDimLE_zero.mpr
  exact Ring.KrullDimLE.of_isLocalization P.asIdeal hP (Localization.AtPrime P.asIdeal)

/-- The target map uses the original ring and its actual prime localization. -/
def targetMap : Spec (.of (Localization.AtPrime P.asIdeal)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P.asIdeal)))

variable {X : Scheme} (f : X ⟶ Spec (.of R)) [LocallyQuasiFinite f] [QuasiCompact f]

/-- The full original source pullback is finite, with no extra component selection. -/
theorem projection_isFinite (hP : P.asIdeal ∈ minimalPrimes R) :
    IsFinite (pullback.snd f (targetMap P)) := by
  let _ := localization_isArtinian P hP
  exact IsFinite.of_locallyQuasiFinite _

/-- With an affine original source, its full local coordinate algebra is finite too. -/
theorem projection_coordinates_finite
    (hP : P.asIdeal ∈ minimalPrimes R) :
    (pullback.snd f (targetMap P)).appTop.hom.Finite := by
  let _ := projection_isFinite P f hP
  exact Scheme.Hom.finite_appTop _

section AffineTarget
variable {Y : Scheme} [IsAffine Y] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [LocallyQuasiFinite g] [QuasiCompact g]
  (Q : PrimeSpectrum Γ(Y, ⊤))

/-- Any original affine Noetherian target is treated through its own section ring. -/
theorem affine_projection_isFinite (hQ : Q.asIdeal ∈ minimalPrimes Γ(Y, ⊤)) :
    IsFinite (pullback.snd g (targetMap Q ≫ Y.isoSpec.inv)) := by
  let _ : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let _ := localization_isArtinian Q hQ
  exact IsFinite.of_locallyQuasiFinite _

end AffineTarget
end FLT.Mazur.SchemeMinimalPrimeFinitePullback

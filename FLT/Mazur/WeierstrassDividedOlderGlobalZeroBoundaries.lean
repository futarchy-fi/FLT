/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSuccessive
public import FLT.Mazur.WeierstrassDividedOlderIndexedIntersections
public import FLT.Mazur.WeierstrassDividedZeroBoundaryFunctions

/-!
# Normalized full first boundary attachments in every retained global model

The first exterior attachment is D(q) and its infinity attachment is D(q*v)
on the complete fiber. Both maps are the original tensor restrictions
transported by the full coordinate equivalence, with cartesian squares.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

local notation "f" => fiberConicFactor a c
local notation "v" => fiberV a c
local notation "E" => zeroResidueFiberIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The full normalized first exterior attachment, using the original boundary map. -/
def olderGlobalZeroToExterior :=
  (zeroHorizontalBoundaryIso D e hk0 hk).hom ≫ olderGlobalHorizontalToExterior hπ data K j hj r hr

/-- The exterior square is cartesian on the entire original first fiber. -/
theorem olderGlobalZeroExterior_isPullback :
    IsPullback (olderGlobalZeroToExterior hπ data D j hj r hr hk0 hk)
      (PrincipalOpenTransport.inclusion (f))
      (olderGlobalExteriorTensorChart hπ data K j hj r hr) g := by
  have H := IsPullback.of_horiz_isIso
    (CategoryTheory.CommSq.mk (zeroHorizontalBoundaryIso_inclusion D e hk0 hk))
  exact H.paste_horiz (olderGlobalExteriorTensor_isPullback hπ data K j hj r hr)

/-- The normalized exterior boundary retains both actual global inclusions. -/
@[reassoc] theorem olderGlobalZeroToExterior_comp :
    olderGlobalZeroToExterior hπ data D j hj r hr hk0 hk ≫
      olderGlobalExteriorTensorChart hπ data K j hj r hr =
        PrincipalOpenTransport.inclusion (f) ≫ g :=
  (olderGlobalZeroExterior_isPullback hπ data D j hj r hr hk0 hk).w

/-- The exact exterior preimage on the full first fiber is its original principal open. -/
theorem olderGlobalZeroExterior_preimage :
    g ⁻¹' Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) =
      (PrimeSpectrum.basicOpen (f) : Set (PrimeSpectrum F)) := by
  have H := olderGlobalZeroExterior_isPullback hπ data D j hj r hr hk0 hk
  have he : g ⁻¹' Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) =
      Set.range (PrincipalOpenTransport.inclusion (f)) := by
    ext z
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback H w z hw
      exact ⟨p, hp⟩
    · rintro ⟨p, rfl⟩
      exact ⟨olderGlobalZeroToExterior hπ data D j hj r hr hk0 hk p,
        congrArg (fun morphism => morphism p) H.w⟩
  rw [he]
  exact PrimeSpectrum.localization_away_comap_range _ (f)

/-- The full normalized first infinity attachment, using the original boundary map. -/
def olderGlobalZeroToInfinity :=
  (zeroInfinityBoundaryIso D e hk0 hk).hom ≫ olderGlobalYToInfinity hπ data K j hj r hr

/-- The infinity square is cartesian on the entire original first fiber. -/
theorem olderGlobalZeroInfinity_isPullback :
    IsPullback (olderGlobalZeroToInfinity hπ data D j hj r hr hk0 hk)
      (PrincipalOpenTransport.inclusion (f * v))
      (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) g := by
  have H := IsPullback.of_horiz_isIso
    (CategoryTheory.CommSq.mk (zeroInfinityBoundaryIso_inclusion D e hk0 hk))
  exact H.paste_horiz (olderGlobalTensor_infinity_isPullback hπ data K j hj r hr)

/-- The normalized infinity boundary retains both actual global inclusions. -/
@[reassoc] theorem olderGlobalZeroToInfinity_comp :
    olderGlobalZeroToInfinity hπ data D j hj r hr hk0 hk ≫
      finiteInfinityTensorChart hπ data K (j + 1 + r) hr =
        PrincipalOpenTransport.inclusion (f * v) ≫ g :=
  (olderGlobalZeroInfinity_isPullback hπ data D j hj r hr hk0 hk).w

/-- The exact infinity preimage on the full first fiber is its original principal open. -/
theorem olderGlobalZeroInfinity_preimage :
    g ⁻¹' Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) =
      (PrimeSpectrum.basicOpen (f * v) : Set (PrimeSpectrum F)) := by
  have H := olderGlobalZeroInfinity_isPullback hπ data D j hj r hr hk0 hk
  have he : g ⁻¹' Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) =
      Set.range (PrincipalOpenTransport.inclusion (f * v)) := by
    ext z
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback H w z hw
      exact ⟨p, hp⟩
    · rintro ⟨p, rfl⟩
      exact ⟨olderGlobalZeroToInfinity hπ data D j hj r hr hk0 hk p,
        congrArg (fun morphism => morphism p) H.w⟩
  rw [he]
  exact PrimeSpectrum.localization_away_comap_range _ (f * v)

end FLT.Mazur.WeierstrassDividedDepth

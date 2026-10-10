/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalCartesian
public import FLT.Mazur.PrincipalOccurrenceCrossChartCoordinates

/-!
# Canonical quotient coordinates on the original comparison domain

The exact quotient ring used by equation descent maps into the original
cross-chart intersection. Its projection is the spectrum of the explicit
localized quotient map in finite cross-chart coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv FiniteRelationLocalization.toQuotient

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))


variable {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)


/-- The exact original quotient ring appearing in cross-chart equation descent. -/
abbrev PrincipalOccurrenceCrossQuotient :=
  FiniteRelationIterated.Quotient R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j)
    (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)

/-- Project the actual finite cross-chart coordinate ring to the canonical quotient. -/
def principalOccurrenceCrossToQuotient :
    PrincipalOccurrenceCrossRing x p q →ₐ[R] PrincipalOccurrenceCrossQuotient e x p q :=
  IsLocalization.Away.mapₐ _ _
    (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j))
    (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)

/-- The quotient map has its prescribed values on every shared-overlap numerator. -/
theorem principalOccurrenceCrossToQuotient_algebraMap
    (z : PrincipalStage R (B j) (b j) (x.target j)) :
    principalOccurrenceCrossToQuotient e x p q (algebraMap _ _ z) =
      algebraMap _ (PrincipalOccurrenceCrossQuotient e x p q)
        (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
          (principalRepresentative R (B j) (b j)) (x.target j) z) := by
  simp [principalOccurrenceCrossToQuotient, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- The quotient spectrum has its natural map to the original shared overlap. -/
def principalOccurrenceCrossQuotientBase :
    Spec (.of (PrincipalOccurrenceCrossQuotient e x p q)) ⟶
      Spec (.of (Localization.Away (b j))) :=
  PrincipalLocalizationSquare.inclusion
    (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)) ≫
    Spec.map (CommRingCat.ofHom (principalQuotientEquiv R (B j) (b j)).symm.toRingHom)

/-- The explicit quotient map commutes with the map to the shared finite overlap. -/
theorem principalOccurrenceCrossQuotient_square :
    Spec.map (CommRingCat.ofHom (principalOccurrenceCrossToQuotient e x p q).toRingHom) ≫
        PrincipalLocalizationSquare.inclusion
          (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q) =
      principalOccurrenceCrossQuotientBase e x p q ≫
        principalOccurrenceOverlapProjection e x j := by
  simp only [principalOccurrenceCrossQuotientBase, principalOccurrenceOverlapProjection,
    PrincipalLocalizationSquare.inclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  change principalOccurrenceCrossToQuotient e x p q (algebraMap _ _ z) =
    algebraMap _ _ ((principalQuotientEquiv R (B j) (b j)).symm
      (principalStageMap R (B j) (b j) (x.target j) z))
  rw [principalOccurrenceCrossToQuotient_algebraMap]
  change _ = algebraMap _ _ ((principalQuotientEquiv R (B j) (b j)).symm
    (principalQuotientEquiv R (B j) (b j) _))
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- The quotient spectrum maps to the actual finite cross-chart scheme. -/
def principalOccurrenceCrossQuotientFinite :
    Spec (.of (PrincipalOccurrenceCrossQuotient e x p q)) ⟶ principalOccurrenceCross x hx p q :=
  Spec.map (CommRingCat.ofHom (principalOccurrenceCrossToQuotient e x p q).toRingHom) ≫
    (principalOccurrenceCrossIso x hx p q).inv

/-- This map has exactly the shared-overlap square needed for cartesian recovery. -/
theorem principalOccurrenceCrossQuotientFinite_fac :
    principalOccurrenceCrossQuotientFinite e x hx p q ≫ principalOccurrenceCrossOpen x hx p q =
      principalOccurrenceCrossQuotientBase e x p q ≫
        principalOccurrenceOverlapProjection e x j := by
  unfold principalOccurrenceCrossQuotientFinite
  rw [Category.assoc, ← principalOccurrenceCrossIso_fac, Iso.inv_hom_id_assoc]
  exact principalOccurrenceCrossQuotient_square e x p q

/-- Lift the canonical quotient coordinates into the actual original atlas intersection. -/
def principalOccurrenceCrossQuotientOriginal :
    Spec (.of (PrincipalOccurrenceCrossQuotient e x p q)) ⟶
      principalOccurrenceOriginalCross e p q :=
  (principalOccurrenceOriginalCrossProjection_isPullback e x hx p q).lift
    (principalOccurrenceCrossQuotientFinite e x hx p q)
    (principalOccurrenceCrossQuotientBase e x p q)
    (principalOccurrenceCrossQuotientFinite_fac e x hx p q)

/-- The lift projects to the explicit quotient map in the actual finite coordinates. -/
@[reassoc (attr := simp)] theorem principalOccurrenceCrossQuotientOriginal_fac :
    principalOccurrenceCrossQuotientOriginal e x hx p q ≫
        principalOccurrenceOriginalCrossProjection e p q x hx =
      principalOccurrenceCrossQuotientFinite e x hx p q :=
  (principalOccurrenceOriginalCrossProjection_isPullback e x hx p q).lift_fst _ _ _

end FLT.Mazur.FiniteTypeRelationModel

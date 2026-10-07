/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreParameters
public import FLT.EllipticCurve.CubicVariableChangeGroup
public import FLT.EllipticCurve.CubicQuadraticEtale
/-! # Local Legendre coordinate symmetries

The substitutions x = 1 - x' and x = λx' are admissible changes after
adjoining a square root of -1 or λ. The corresponding finite étale
surjective covers and actual isomorphisms over them are constructed here.
Over reduced noetherian bases the coordinate isomorphisms preserve the group law.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- The coordinate change exchanging the roots zero and one. -/
def legendreSwapChange (u : Rˣ) : VariableChange R := ⟨u, 1, 0, 0⟩
/-- The coordinate scaling exchanging one and the unit parameter. -/
def legendreReciprocalChange (u : Rˣ) : VariableChange R := ⟨u, 0, 0, 0⟩

/-- A square root of -1 realizes the parameter change λ ↦ 1-λ. -/
theorem legendreSwapChange_curve (l : R) (u : Rˣ) (hu : (u : R) ^ 2 = -1) :
    legendreSwapChange u • legendreCurve l = legendreCurve (1 - l) := by
  have hi : ((u⁻¹ : Rˣ) : R) ^ 2 = -1 := by
    have h := pow_mul_pow_eq_one 2 u.inv_mul
    rw [hu] at h
    linear_combination -h
  have hi4 : ((u⁻¹ : Rˣ) : R) ^ 4 = 1 := by
    calc _ = (((u⁻¹ : Rˣ) : R) ^ 2) ^ 2 := by ring
         _ = 1 := by rw [hi]; ring
  ext <;> simp [legendreSwapChange, variableChange_def, legendreCurve, hi, hi4] <;> ring

/-- A square root of λ realizes the parameter change λ ↦ λ⁻¹. -/
theorem legendreReciprocalChange_curve (l u : Rˣ) (hu : (u : R) ^ 2 = l) :
    legendreReciprocalChange u • legendreCurve (l : R) =
      legendreCurve ((l⁻¹ : Rˣ) : R) := by
  have hi : ((u⁻¹ : Rˣ) : R) ^ 2 = (l⁻¹ : Rˣ) := by
    have h := pow_mul_pow_eq_one 2 u.inv_mul
    rw [hu] at h
    calc _ = (((u⁻¹ : Rˣ) : R) ^ 2 * (l : R)) * (l⁻¹ : Rˣ) := by
                rw [mul_assoc, l.mul_inv, mul_one]
         _ = _ := by rw [h, one_mul]
  have hi4 : ((u⁻¹ : Rˣ) : R) ^ 4 = ((l⁻¹ : Rˣ) : R) ^ 2 := by
    calc _ = (((u⁻¹ : Rˣ) : R) ^ 2) ^ 2 := by ring
         _ = _ := by rw [hi]
  ext <;> simp [legendreReciprocalChange, variableChange_def, legendreCurve, hi, hi4]
  · linear_combination -l.inv_mul
  · linear_combination ((l⁻¹ : Rˣ) : R) * l.inv_mul


/-- The Legendre equation commutes with coefficient maps. -/
theorem legendreCurve_map {S : Type*} [CommRing S] (f : R →+* S) (l : R) :
    (legendreCurve l).map f = legendreCurve (f l) := by
  ext <;> simp [legendreCurve, WeierstrassCurve.map]

/-- A coordinate isomorphism with its transformed equation identified explicitly. -/
def variableChangeCongrOverIso (W V : WeierstrassCurve R) (C : VariableChange R)
    (h : C • W = V) : groupModel V ≅ groupModel W :=
  eqToIso (congrArg groupModel h.symm) ≪≫ variableChangeOverIso W C

open MonoidalCategory MonObj

/-- Identifying the transformed equation preserves the group morphism. -/
instance variableChangeCongrOverIsoIsMonHom [IsNoetherianRing R] [_root_.IsReduced R]
    (W V : WeierstrassCurve R) (C : VariableChange R)
    [W.IsElliptic] [V.IsElliptic] (h : C • W = V) :
    IsMonHom (variableChangeCongrOverIso W V C h).hom := by
  subst V
  simpa only [variableChangeCongrOverIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.id_comp] using (inferInstance : IsMonHom (variableChangeOverIso W C).hom)

/-- The actual curve isomorphism associated to λ ↦ 1-λ. -/
def legendreSwapOverIso (l : R) (u : Rˣ) (hu : (u : R) ^ 2 = -1) :
    groupModel (legendreCurve (1 - l)) ≅ groupModel (legendreCurve l) :=
  variableChangeCongrOverIso (legendreCurve l) (legendreCurve (1 - l))
    (legendreSwapChange u) (legendreSwapChange_curve l u hu)

/-- The actual curve isomorphism associated to λ ↦ λ⁻¹. -/
def legendreReciprocalOverIso (l u : Rˣ) (hu : (u : R) ^ 2 = l) :
    groupModel (legendreCurve ((l⁻¹ : Rˣ) : R)) ≅ groupModel (legendreCurve (l : R)) :=
  variableChangeCongrOverIso (legendreCurve (l : R)) (legendreCurve ((l⁻¹ : Rˣ) : R))
    (legendreReciprocalChange u) (legendreReciprocalChange_curve l u hu)

/-- The coefficient cover adjoining a square root of -1. -/
abbrev LegendreSwapRing (R : Type u) [CommRing R] :=
  QuadraticEtaleRing (-1 : Rˣ)

/-- The actual cover on which swapping zero and one is defined. -/
def legendreSwapCover (R : Type u) [CommRing R] :
    Spec (.of (LegendreSwapRing R)) ⟶ Spec (.of R) :=
  quadraticEtaleCover (-1 : Rˣ)

/-- The local Legendre swap over the constructed square-root cover. -/
def legendreSwapLocalIso (l : R) :
    groupModel (legendreCurve (1 - algebraMap R (LegendreSwapRing R) l)) ≅
      groupModel (legendreCurve (algebraMap R (LegendreSwapRing R) l)) :=
  legendreSwapOverIso _ (quadraticEtaleUnit (-1 : Rˣ)) (by
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using
      quadraticEtaleUnit_square (-1 : Rˣ))

/-- The coefficient cover adjoining a square root of the unit parameter. -/
abbrev LegendreReciprocalRing (l : Rˣ) := QuadraticEtaleRing l

/-- The actual cover on which reciprocal scaling is defined. -/
def legendreReciprocalCover (l : Rˣ) :
    Spec (.of (LegendreReciprocalRing l)) ⟶ Spec (.of R) :=
  quadraticEtaleCover l

/-- The local reciprocal isomorphism over the constructed cover. -/
def legendreReciprocalLocalIso (l : Rˣ) :
    groupModel (legendreCurve (algebraMap R (LegendreReciprocalRing l) ((l⁻¹ : Rˣ) : R))) ≅
      groupModel (legendreCurve (algebraMap R (LegendreReciprocalRing l) (l : R))) := by
  let l' : (LegendreReciprocalRing l)ˣ :=
    Units.map (algebraMap R (LegendreReciprocalRing l)) l
  exact legendreReciprocalOverIso l' (quadraticEtaleUnit l) (quadraticEtaleUnit_square l)

/-- The swap cover is étale. -/
instance legendreSwapCoverEtale : Etale (legendreSwapCover R) :=
  inferInstanceAs (Etale (quadraticEtaleCover (-1 : Rˣ)))

/-- The swap cover is finite when 2 is invertible. -/
instance legendreSwapCoverFinite [Fact (IsUnit (2 : R))] :
    IsFinite (legendreSwapCover R) :=
  inferInstanceAs (IsFinite (quadraticEtaleCover (-1 : Rˣ)))

/-- The swap cover is surjective when 2 is invertible. -/
instance legendreSwapCoverSurjective [Nontrivial R] [Fact (IsUnit (2 : R))] :
    Surjective (legendreSwapCover R) :=
  inferInstanceAs (Surjective (quadraticEtaleCover (-1 : Rˣ)))

/-- The reciprocal cover is étale. -/
instance legendreReciprocalCoverEtale (l : Rˣ) : Etale (legendreReciprocalCover l) :=
  inferInstanceAs (Etale (quadraticEtaleCover l))

/-- The reciprocal cover is finite when 2 is invertible. -/
instance legendreReciprocalCoverFinite (l : Rˣ) [Fact (IsUnit (2 : R))] :
    IsFinite (legendreReciprocalCover l) :=
  inferInstanceAs (IsFinite (quadraticEtaleCover l))

/-- The reciprocal cover is surjective when 2 is invertible. -/
instance legendreReciprocalCoverSurjective (l : Rˣ) [Nontrivial R] [Fact (IsUnit (2 : R))] :
    Surjective (legendreReciprocalCover l) :=
  inferInstanceAs (Surjective (quadraticEtaleCover l))


/-- The swap isomorphism preserves the group law. -/
instance legendreSwapOverIsoIsMonHom [IsNoetherianRing R] [_root_.IsReduced R]
    (l : R) (u : Rˣ) (hu : (u : R) ^ 2 = -1)
    [(legendreCurve l).IsElliptic] [(legendreCurve (1 - l)).IsElliptic] :
    IsMonHom (legendreSwapOverIso l u hu).hom :=
  inferInstanceAs (IsMonHom (variableChangeCongrOverIso _ _ _ _).hom)

/-- The reciprocal isomorphism preserves the group law. -/
instance legendreReciprocalOverIsoIsMonHom [IsNoetherianRing R] [_root_.IsReduced R]
    (l u : Rˣ) (hu : (u : R) ^ 2 = l)
    [(legendreCurve (l : R)).IsElliptic] [(legendreCurve ((l⁻¹ : Rˣ) : R)).IsElliptic] :
    IsMonHom (legendreReciprocalOverIso l u hu).hom :=
  inferInstanceAs (IsMonHom (variableChangeCongrOverIso _ _ _ _).hom)

end WeierstrassCurve.CubicCharts

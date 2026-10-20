/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChosenBasisCharpoly
public import FLT.Mazur.AffineNormCartesianCharts

/-!
# Coefficients on independent finite free affine charts

Each coefficient lives in the original structure sheaf. Restriction and
arbitrary cartesian base change compare independently chosen local bases of
the whole source preimages, including charts whose ranks differ.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.AffineCharpolyCharts
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- One coefficient on an actual affine target chart with a finite free whole preimage. -/
def chart (U : Y.affineOpens) (hU : AffineOpenNorm.HasBasis f U)
    (s : Γ(X, ⊤)) (n : ℕ) : Γ(Y, U.1) :=
  U.1.topIso.hom ((AffineChosenBasisCharpoly.charpoly (f ∣_ U.1) hU
    ((f ⁻¹ᵁ U.1).ι.appTop s)).coeff n)

/-- The chart coefficient in the section ring of the open subscheme. -/
theorem chart_top (U : Y.affineOpens) (hU : AffineOpenNorm.HasBasis f U)
    (s : Γ(X, ⊤)) (n : ℕ) :
    U.1.topIso.inv (chart f U hU s n) =
      (AffineChosenBasisCharpoly.charpoly (f ∣_ U.1) hU
        ((f ⁻¹ᵁ U.1).ι.appTop s)).coeff n := by
  exact Iso.hom_inv_id_apply _ _

variable [IsAffineHom f]

/-- All coefficients commute with restriction to a separately based smaller chart. -/
theorem chart_restrict {U V : Y.affineOpens} (hU : AffineOpenNorm.HasBasis f U)
    (hV : AffineOpenNorm.HasBasis f V) (h : V ≤ U) (s : Γ(X, ⊤)) (n : ℕ) :
    Y.presheaf.map (homOfLE h).op (chart f U hU s n) = chart f V hV s n := by
  let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  unfold chart
  erw [Approximation.topIso_hom_restriction (X := Y) h]
  congr 1
  have hc := congrArg (fun P ↦ P.coeff n)
    (AffineChosenBasisCharpoly.charpoly_pullback (f ∣_ U.1)
      (AffinePreimageRestriction.isPullback f h) hU hV ((f ⁻¹ᵁ U.1).ι.appTop s))
  rw [coeff_map] at hc
  rw [← hc]
  congr 3
  exact congrArg (fun k : (f ⁻¹ᵁ V.1).toScheme ⟶ X ↦ k.appTop s)
    (Scheme.homOfLE_ι X (f.preimage_mono h))

variable {P T : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ T} {g : T ⟶ Y}
  (H : IsPullback a b f g)

include H in
/-- Cartesian transport compares each coefficient on unrelated actual target charts. -/
theorem chart_pullback (U : Y.affineOpens) (V : T.affineOpens)
    (h : V.1 ≤ g ⁻¹ᵁ U.1) (hU : AffineOpenNorm.HasBasis f U)
    (hV : AffineOpenNorm.HasBasis b V) (s : Γ(X, ⊤)) (n : ℕ) :
    chart b V hV (a.appTop s) n = g.appLE U.1 V.1 h (chart f U hU s n) := by
  let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  apply (ConcreteCategory.bijective_of_isIso V.1.topIso.inv).injective
  rw [chart_top]
  have ht : V.1.topIso.inv (g.appLE U.1 V.1 h (chart f U hU s n)) =
      (g.resLE U.1 V.1 h).appTop (U.1.topIso.inv (chart f U hU s n)) := by
    have he := Approximation.topIso_hom_resLE g U.1 V.1 h
      (U.1.topIso.inv (chart f U hU s n))
    simpa only [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply] using
      congrArg V.1.topIso.inv he
  rw [ht, chart_top]
  have hc := congrArg (fun Q ↦ Q.coeff n)
    (AffineChosenBasisCharpoly.charpoly_pullback (f ∣_ U.1)
      (AffineNormCartesianCharts.isPullback H U V h) hU hV
      ((f ⁻¹ᵁ U.1).ι.appTop s))
  rw [coeff_map] at hc
  rw [← hc]
  congr 3
  exact congrArg (fun k : (b ⁻¹ᵁ V.1).toScheme ⟶ X ↦ k.appTop s)
    (Scheme.Hom.resLE_comp_ι a (AffineNormCartesianCharts.source_le H U V h)).symm

end FLT.Mazur.AffineCharpolyCharts

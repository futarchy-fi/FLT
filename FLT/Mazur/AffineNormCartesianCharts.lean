/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNormGluingFiber

/-!
# Cartesian change of genuine local norm charts

An arbitrary cartesian square transports whole-preimage bases and their norms.
Only the two selected target charts must be affine; the original target
charts are not required to be invariant under a relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineNormCartesianCharts
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T Y : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ T}
  {f : X ⟶ Y} {g : T ⟶ Y} (H : IsPullback a b f g)
  [IsAffineHom f]
  (U : Y.affineOpens) (V : T.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1)

include H h

omit [IsAffineHom f] in
/-- The entire changed preimage lies over the original source chart. -/
theorem source_le : b ⁻¹ᵁ V.1 ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U.1) := by
  rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  exact b.preimage_mono h

omit [IsAffineHom f] in
/-- Restricting both targets retains the whole cartesian source. -/
theorem isPullback :
    IsPullback (a.resLE (f ⁻¹ᵁ U.1) (b ⁻¹ᵁ V.1) (source_le H U V h))
      (b ∣_ V.1) (f ∣_ U.1) (g.resLE U.1 V.1 h) := by
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    Scheme.Hom.isPullback_resLE H h le_rfl
      (inf_eq_right.mpr (source_le H U V h)).symm

/-- The basis belongs to every point of the changed source preimage. -/
theorem hasBasis (hU : AffineOpenNorm.HasBasis f U) : AffineOpenNorm.HasBasis b V := by
  let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let _ := (f ∣_ U.1).appTop.hom.toAlgebra
  let _ := (b ∣_ V.1).appTop.hom.toAlgebra
  obtain ⟨n, ⟨basis⟩⟩ := hU
  exact ⟨n, ⟨AffineCartesianNorm.sectionBasis _ _ _ _ (isPullback H U V h) basis⟩⟩

/-- The norm on the changed chart is the actual pullback of the original local norm. -/
theorem chart_pullback (hU : AffineOpenNorm.HasBasis f U) (s : Γ(X, ⊤)) :
    AffineNormGluing.chart b V (a.appTop s) =
      g.appLE U.1 V.1 h (AffineNormGluing.chart f U s) := by
  let _ : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let _ := (f ∣_ U.1).appTop.hom.toAlgebra
  obtain ⟨n, ⟨basis⟩⟩ := hU
  apply (ConcreteCategory.bijective_of_isIso V.1.topIso.inv).injective
  rw [AffineNormGluing.chart_top]
  have ht : V.1.topIso.inv (g.appLE U.1 V.1 h (AffineNormGluing.chart f U s)) =
      (g.resLE U.1 V.1 h).appTop
        (U.1.topIso.inv (AffineNormGluing.chart f U s)) := by
    have he := Approximation.topIso_hom_resLE g U.1 V.1 h
      (U.1.topIso.inv (AffineNormGluing.chart f U s))
    simpa only [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply] using
      congrArg V.1.topIso.inv he
  rw [ht, AffineNormGluing.chart_top,
    ← AffineRelationNorm.sectionNorm_pullback (isPullback H U V h) basis]
  congr 1
  exact congrArg (fun k : (b ⁻¹ᵁ V.1).toScheme ⟶ X ↦ k.appTop s)
    (Scheme.Hom.resLE_comp_ι a (source_le H U V h)).symm

end FLT.Mazur.AffineNormCartesianCharts

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNormChartIndependence
public import FLT.Mazur.AffineSectionNormFiber

/-!
# Full fibers of the norm glued from local bases

The nonvanishing test concerns every point of the original morphism's fiber.
It does not require a common rank, a global basis, or invariant target charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineNormGluing
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]

omit [IsAffineHom f] [IsAffine Y] in
/-- Original global sections restrict through the canonical top-section comparison. -/
theorem topIso_inv_global (U : X.Opens) (s : Γ(X, ⊤)) :
    U.topIso.inv (X.presheaf.map (homOfLE le_top).op s) = U.ι.appTop s := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

omit [IsAffineHom f] [IsAffine Y] in
/-- A chart's top-section norm uses the actual inclusion of the whole source preimage. -/
theorem chart_top (U : Y.affineOpens) (s : Γ(X, ⊤)) :
    U.1.topIso.inv (chart f U s) = AffineRelationNorm.sectionNorm (f ∣_ U.1)
      ((f ⁻¹ᵁ U.1).ι.appTop s) := by
  unfold chart AffineOpenNorm.norm
  rw [Iso.hom_inv_id_apply, topIso_inv_global]

variable {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- The norm on the target chart is the determinant of the entire restricted source. -/
theorem norm_top (i : ι) (s : Γ(X, ⊤)) :
    (U i).1.ι.appTop (norm f U hU hcover s) =
      AffineRelationNorm.sectionNorm (f ∣_ (U i).1)
        ((f ⁻¹ᵁ (U i).1).ι.appTop s) := by
  rw [← topIso_inv_global, norm_chart, chart_top]

/-- The glued norm is nonvanishing exactly when every original fiber point avoids zero. -/
theorem mem_basicOpen_norm_iff (s : Γ(X, ⊤)) (y : Y) :
    y ∈ Y.basicOpen (norm f U hU hcover s) ↔
      ∀ x : X, f x = y → x ∈ X.basicOpen s := by
  obtain ⟨i, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show y ∈ ⨆ i, (U i).1 from hcover.symm ▸ trivial)
  let V := (U i).1
  let z : V.toScheme := ⟨y, hy⟩
  let _ : IsAffine (f ⁻¹ᵁ V).toScheme := (U i).2.preimage f
  let _ := (f ∣_ V).appTop.hom.toAlgebra
  obtain ⟨n, ⟨b⟩⟩ := hU i
  have hc : y ∈ Y.basicOpen (norm f U hU hcover s) ↔
      z ∈ V.toScheme.basicOpen (V.ι.appTop (norm f U hU hcover s)) := by
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  rw [hc, norm_top]
  change z ∈ V.toScheme.basicOpen (Algebra.norm Γ(V, ⊤) _) ↔ _
  rw [AffineSectionNormFiber.mem_basicOpen_norm_iff (f ∣_ V) b]
  constructor
  · intro h x hx
    let w : (f ⁻¹ᵁ V).toScheme := ⟨x, by change f x ∈ V; simpa [hx] using hy⟩
    have hw : (f ∣_ V) w = z := by
      apply Subtype.ext
      exact (morphismRestrict_base_coe f V w).trans hx
    have hm := h w hw
    rw [← Scheme.preimage_basicOpen_top] at hm
    exact hm
  · intro h w hw
    rw [← Scheme.preimage_basicOpen_top]
    apply h w.1
    exact (morphismRestrict_base_coe f V w).symm.trans (congrArg Subtype.val hw)

end FLT.Mazur.AffineNormGluing

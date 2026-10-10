/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientUniversalFamily

/-!
# Intersections and inclusions of actual Hilbert support opens

The full-family support condition preserves intersections and the whole
ambient. Inclusions of ambient opens induce actual open immersions between
their Hilbert representatives, with strict identity and composition laws.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

variable (R I : Type u) [CommRing R] (d : ℕ) (K : Ideal (MvPolynomial I R))
variable (U V W : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)

/-- A larger ambient open allows every family allowed by the smaller one. -/
theorem ambientHilbertSupportOpen_mono (h : U ≤ V) :
    ambientHilbertSupportOpen R I d K U ≤ ambientHilbertSupportOpen R I d K V := by
  intro x hx
  exact (mem_quotientFamilySupportOpen _ _ _ _ _ _ _ x).mpr fun z hz ↦
    h ((mem_quotientFamilySupportOpen _ _ _ _ _ _ _ x).mp hx z hz)

/-- Support in an ambient intersection is exactly simultaneous support in both opens. -/
theorem ambientHilbertSupportOpen_inf :
    ambientHilbertSupportOpen R I d K (U ⊓ V) =
      ambientHilbertSupportOpen R I d K U ⊓ ambientHilbertSupportOpen R I d K V := by
  apply le_antisymm
  · exact le_inf (ambientHilbertSupportOpen_mono R I d K _ _ inf_le_left)
      (ambientHilbertSupportOpen_mono R I d K _ _ inf_le_right)
  · intro x hx
    apply (mem_quotientFamilySupportOpen _ _ _ _ _ _ _ x).mpr
    intro z hz
    exact ⟨(mem_quotientFamilySupportOpen _ _ _ _ _ _ _ x).mp hx.1 z hz,
      (mem_quotientFamilySupportOpen _ _ _ _ _ _ _ x).mp hx.2 z hz⟩

/-- The entire ambient permits every family, including the empty degree-zero family. -/
theorem ambientHilbertSupportOpen_top : ambientHilbertSupportOpen R I d K ⊤ = ⊤ := by
  apply top_unique
  intro x _
  exact (mem_quotientFamilySupportOpen _ _ _ _ _ _ _ x).mpr fun _ _ ↦ trivial

/-- Ambient inclusion gives an actual inclusion of the constructed Hilbert representatives. -/
def openAmbientHilbertInclusion (h : U ≤ V) :
    (ambientHilbertSupportOpen R I d K U).toScheme ⟶
      (ambientHilbertSupportOpen R I d K V).toScheme :=
  (ambientHilbertScheme R I d K).homOfLE (ambientHilbertSupportOpen_mono R I d K U V h)

instance (h : U ≤ V) : IsOpenImmersion (openAmbientHilbertInclusion R I d K U V h) := by
  unfold openAmbientHilbertInclusion
  infer_instance

/-- The Hilbert inclusion is the literal inclusion into the original affine Hilbert scheme. -/
@[reassoc]
theorem openAmbientHilbertInclusion_ι (h : U ≤ V) :
    openAmbientHilbertInclusion R I d K U V h ≫ (ambientHilbertSupportOpen R I d K V).ι =
      (ambientHilbertSupportOpen R I d K U).ι := Scheme.homOfLE_ι _ _

/-- The Hilbert inclusion preserves the coefficient-base structure. -/
@[reassoc]
theorem openAmbientHilbertInclusion_over (h : U ≤ V) :
    openAmbientHilbertInclusion R I d K U V h ≫ openAmbientHilbertStructure R I d K V =
      openAmbientHilbertStructure R I d K U := by
  unfold openAmbientHilbertStructure
  rw [← Category.assoc, openAmbientHilbertInclusion_ι]

/-- Identity ambient inclusion gives identity Hilbert inclusion. -/
theorem openAmbientHilbertInclusion_refl :
    openAmbientHilbertInclusion R I d K U U le_rfl = 𝟙 _ := Scheme.homOfLE_rfl _ _

/-- Nested ambient inclusions compose as actual Hilbert scheme maps. -/
theorem openAmbientHilbertInclusion_trans (h : U ≤ V) (k : V ≤ W) :
    openAmbientHilbertInclusion R I d K U V h ≫ openAmbientHilbertInclusion R I d K V W k =
      openAmbientHilbertInclusion R I d K U W (h.trans k) := Scheme.homOfLE_homOfLE _ _ _

end FLT.Mazur.HilbertChart

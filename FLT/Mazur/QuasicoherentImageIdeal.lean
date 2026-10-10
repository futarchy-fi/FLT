/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineChartSectionLocalization
public import FLT.Mazur.GlobalIdealPowerCompatibility

/-!
# The full image ideal of a quasi-coherent sheaf map

The affine ranges of a map to the structure sheaf localize, and hence define
an actual ideal sheaf. No radical is taken, so the closed subscheme retains
multiplicities and nilpotents. An injective map identifies its source with
the module sheaf of this ideal.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {M : X.Modules} (a : M ⟶ structureModule X)

/-- The full affine range, regarded as an ideal of the coordinate ring. -/
def affineImageIdeal (U : X.affineOpens) : Ideal Γ(X, U) :=
  LinearMap.range (a.val.app (op U.1)).hom

/-- Affine image ideals commute with principal localization. -/
theorem affineImageIdeal_map_basicOpen [M.IsQuasicoherent]
    (U : X.affineOpens) (r : Γ(X, U)) :
    (affineImageIdeal a U).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      affineImageIdeal a (X.affineBasicOpen r) := by
  let ρ := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have hn (s : Γ(M, U.1)) :
      ρ (a.app U.1 s) = a.app (X.basicOpen r)
        (M.presheaf.map (homOfLE (X.basicOpen_le r)).op s) :=
    (ConcreteCategory.congr_hom (a.val.naturality (homOfLE (X.basicOpen_le r)).op) s).symm
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro _ ⟨s, rfl⟩
    exact ⟨_, (hn s).symm⟩
  · rintro _ ⟨s, rfl⟩
    let q := AffineChartSectionLocalization.restriction M U (X.basicOpen_le r)
      le_rfl (homOfLE (X.basicOpen_le r))
    have := AffineChartSectionLocalization.restriction_isLocalized M U r
    obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj q r s
    have he : ρ (r ^ n) *
        (show Γ(X, X.basicOpen r) from a.app (X.basicOpen r) s) = ρ (a.app U.1 t) := by
      rw [hn]
      change ρ (r ^ n) • a.app (X.basicOpen r) s = _
      rw [← Hom.app_smul]
      exact congrArg (a.app (X.basicOpen r)) ht
    have hu : IsUnit (ρ (r ^ n)) := by
      rw [map_pow]
      exact (X.toRingedSpace.isUnit_res_basicOpen r).pow n
    apply (Ideal.unit_mul_mem_iff_mem _ hu).mp
    change ρ (r ^ n) * (show Γ(X, X.basicOpen r) from a.app _ s) ∈ _
    rw [he]
    exact Ideal.mem_map_of_mem ρ ⟨t, rfl⟩

/-- The actual quasi-coherent image ideal, with its full affine ideals. -/
def quasicoherentImageIdeal [M.IsQuasicoherent] : X.IdealSheafData where
  ideal := affineImageIdeal a
  map_ideal_basicOpen := affineImageIdeal_map_basicOpen a

/-- The constructed ideal has exactly the original affine image. -/
lemma quasicoherentImageIdeal_ideal [M.IsQuasicoherent] (U : X.affineOpens) :
    (quasicoherentImageIdeal a).ideal U = LinearMap.range (a.val.app (op U.1)).hom := rfl

/-- An injective map recovers its source as the module of its full image ideal. -/
def quasicoherentImageIdealIso [M.IsQuasicoherent] [Mono a] :
    M ≅ idealModule (quasicoherentImageIdeal a) :=
  GlobalIdealPowerCompatibility.affineImageIso a (idealModuleι _) (fun U ↦ by
    apply SetLike.coe_injective
    exact (idealModuleι_range (quasicoherentImageIdeal a) U).symm)

/-- Recovery respects the actual inclusion into the structure sheaf. -/
@[reassoc (attr := simp)]
lemma quasicoherentImageIdealIso_comp [M.IsQuasicoherent] [Mono a] :
    (quasicoherentImageIdealIso a).hom ≫ idealModuleι _ = a :=
  GlobalIdealPowerCompatibility.affineImageIso_comp _ _ _

end FLT.Mazur.FCurve

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealPullbackComparison

/-!
# Flat pullback of full Cartier ideals

Flat affine section maps preserve regular chart equations. Consequently every
flat pullback of a full Cartier ideal is Cartier and the canonical ideal-module
comparison is invertible. Neither the schemes nor the divisor are assumed reduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}}

/-- A regular equation remains regular under a flat ring homomorphism. -/
theorem isRegular_map_of_flat {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat) {a : A} (ha : IsRegular a) : IsRegular (φ a) := by
  let : Algebra A B := φ.toAlgebra
  let : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp hφ
  rw [← isLeftRegular_iff_isRegular]
  simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
    (Module.Flat.isSMulRegular_of_isRegular (M := B) ha)

/-- A full Cartier ideal remains Cartier along every flat scheme morphism. -/
theorem EffectiveCartier.comap_of_flat {I : Y.IdealSheafData}
    (hI : EffectiveCartier I) (f : X ⟶ Y) [Flat f] : EffectiveCartier (I.comap f) := by
  intro x
  obtain ⟨U, hxU, a, ha, hIa⟩ := hI (f x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U.1).isOpen
  refine ⟨⟨V, hV⟩, hxV, (f.appLE U.1 V hVU).hom a,
    isRegular_map_of_flat _ (f.flat_appLE U.2 hV hVU) ha, ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap I f U ⟨V, hV⟩ hVU,
    hIa, Ideal.map_span, Set.image_singleton]

/-- The canonical actual ideal-module comparison is invertible for flat Cartier pullback. -/
theorem idealModulePullbackHom_isIso_of_flat (I : Y.IdealSheafData)
    (hI : EffectiveCartier I) (f : X ⟶ Y) [Flat f] :
    IsIso (idealModulePullbackHom I f) :=
  idealModulePullbackHom_isIso_of_cartier f hI (hI.comap_of_flat f)

end FLT.Mazur.FCurve

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualPrincipalAmbient

/-!
# Actual principal section spectra inside the full residual target

Localization identifies the spectrum of actual quotient sections on each
residual principal domain with the corresponding open subscheme of the full
residual spectrum. The comparison keeps the original restriction of sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n) (s : affineResidualSections n i)

/-- The scheme map induced by the actual residual restriction on quotient sections. -/
def affineResidualPrincipalSpectrumMap :
    invariantAffineTarget n (affineResidualAmbientPrincipal n i s) ⟶
      affineResidualSpectrum n i :=
  Spec.map (CommRingCat.ofHom (affineResidualPrincipalRestriction n i s))

/-- The ordinary basic open in the full residual spectrum. -/
def affineResidualSpectrumBasicOpen : (affineResidualSpectrum n i).Opens :=
  PrimeSpectrum.basicOpen s

/-- Actual principal restriction embeds its section spectrum as an open subscheme. -/
instance affineResidualPrincipalSpectrumMap_isOpenImmersion :
    IsOpenImmersion (affineResidualPrincipalSpectrumMap n i s) := by
  let _ := (affineResidualPrincipalRestriction n i s).toAlgebra
  let _ := affineResidualPrincipalRestriction_isLocalization n i s
  exact IsOpenImmersion.of_isLocalization s

/-- The original restriction image is precisely the expected full residual spectrum basic open. -/
theorem affineResidualPrincipalSpectrumMap_range :
    Set.range (affineResidualPrincipalSpectrumMap n i s) =
      (affineResidualSpectrumBasicOpen n i s).carrier := by
  let _ := (affineResidualPrincipalRestriction n i s).toAlgebra
  let _ := affineResidualPrincipalRestriction_isLocalization n i s
  exact PrimeSpectrum.localization_away_comap_range
    ((invariantSheaf n).obj.obj (Opposite.op (affineResidualAmbientPrincipal n i s))) s

/-- The actual section spectrum of a residual principal domain is its target basic open. -/
def affineResidualPrincipalSpectrumIso :
    invariantAffineTarget n (affineResidualAmbientPrincipal n i s) ≅
      (affineResidualSpectrumBasicOpen n i s).toScheme :=
  IsOpenImmersion.isoOfRangeEq (affineResidualPrincipalSpectrumMap n i s)
    (affineResidualSpectrumBasicOpen n i s).ι (by
      rw [affineResidualPrincipalSpectrumMap_range, Scheme.Opens.range_ι]
      rfl)

/-- This open-subscheme identification retains the exact residual restriction morphism. -/
@[reassoc] theorem affineResidualPrincipalSpectrumIso_inclusion :
    (affineResidualPrincipalSpectrumIso n i s).hom ≫
      (affineResidualSpectrumBasicOpen n i s).ι =
        affineResidualPrincipalSpectrumMap n i s :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.CyclicCharacteristicOrbit

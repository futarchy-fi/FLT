/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteUnramifiedConstantFiber
public import FLT.Mazur.UniversalWeierstrassFourTorsionUnramified

/-!
# The universal four-torsion scheme is finite etale of rank sixteen

The coefficient ring is reduced. Formal unramifiedness and the constant
geometric point count therefore prove flatness of the actual torsion equation.
Finite presentation upgrades this to etaleness over the entire parameter base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

/-- The full universal torsion equation is flat over the original parameter ring. -/
instance fourTorsion_flat : Flat fourTorsion.hom := by
  apply FiniteUnramifiedConstantFiber.flat_of_geometric_card fourTorsion.hom 16
  intro K _ _ _
  exact fourTorsionGeometricFiber_card K

/-- The actual universal four-torsion scheme is finite etale, including in characteristic three. -/
instance fourTorsion_etale : Etale fourTorsion.hom := by
  let _ : IsLocallyNoetherian parameterBase :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of ParameterRing)))
  exact Etale.of_formallyUnramified_of_flat _

/-- Etaleness persists under every change of coefficient base. -/
instance fourTorsion_baseChange_etale {T : Scheme} (g : T ⟶ parameterBase) :
    Etale (pullback.snd fourTorsion.hom g) := inferInstance

/-- The finite locally free rank is sixteen at every parameter, not only at geometric tests. -/
theorem fourTorsion_rank (s : parameterBase) : fourTorsion.hom.finrank s = 16 := by
  let p : PrimeSpectrum ParameterRing := s
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let g : Spec (.of K) ⟶ parameterBase := Spec.map (CommRingCat.ofHom (algebraMap ParameterRing K))
  let t : Spec (.of K) := IsLocalRing.closedPoint K
  have hs : g t = s := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap ParameterRing K) (IsLocalRing.maximalIdeal K) = p.asIdeal
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
      IsScalarTower.algebraMap_eq ParameterRing p.asIdeal.ResidueField K,
      RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField K).injective,
      Ideal.ker_algebraMap_residueField]
  calc
    fourTorsion.hom.finrank s = fourTorsion.hom.finrank (g t) :=
      congrArg fourTorsion.hom.finrank hs.symm
    _ = (pullback.snd fourTorsion.hom g).finrank t :=
      (Scheme.Hom.finrank_pullback_snd fourTorsion.hom g t).symm
    _ = 16 := fourTorsionGeometricFiber_rank K t

end FLT.Mazur.UniversalWeierstrass

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteUnramifiedConstantFiber
public import FLT.Mazur.OddWeierstrassThreeTorsionUnramified

/-!
# The universal three-torsion scheme is finite etale of rank nine

The coefficient ring is reduced. Formal unramifiedness and the constant
geometric point count therefore prove flatness of the actual torsion equation.
Finite presentation upgrades this to etaleness over the entire parameter base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing oddChartEquation oddChart_discriminant
  oddChart_three_isUnit)

/-- The full universal torsion equation is flat over the original parameter ring. -/
instance threeTorsion_flat : Flat threeTorsion.hom := by
  apply FiniteUnramifiedConstantFiber.flat_of_geometric_card threeTorsion.hom 9
  intro K _ _ _
  exact threeTorsionGeometricFiber_card K

/-- The actual universal three-torsion scheme is finite etale, including in characteristic two. -/
instance threeTorsion_etale : Etale threeTorsion.hom := by
  let _ : IsLocallyNoetherian parameterBase :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of OddChartRing)))
  exact Etale.of_formallyUnramified_of_flat _

/-- Etaleness persists under every change of coefficient base. -/
instance threeTorsion_baseChange_etale {T : Scheme} (g : T ⟶ parameterBase) :
    Etale (pullback.snd threeTorsion.hom g) := inferInstance

/-- The finite locally free rank is nine at every parameter, not only at geometric tests. -/
theorem threeTorsion_rank (s : parameterBase) : threeTorsion.hom.finrank s = 9 := by
  let p : PrimeSpectrum OddChartRing := s
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let g : Spec (.of K) ⟶ parameterBase := Spec.map (CommRingCat.ofHom (algebraMap OddChartRing K))
  let t : Spec (.of K) := IsLocalRing.closedPoint K
  have hs : g t = s := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap OddChartRing K) (IsLocalRing.maximalIdeal K) = p.asIdeal
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
      IsScalarTower.algebraMap_eq OddChartRing p.asIdeal.ResidueField K,
      RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField K).injective,
      Ideal.ker_algebraMap_residueField]
  calc
    threeTorsion.hom.finrank s = threeTorsion.hom.finrank (g t) :=
      congrArg threeTorsion.hom.finrank hs.symm
    _ = (pullback.snd threeTorsion.hom g).finrank t :=
      (Scheme.Hom.finrank_pullback_snd threeTorsion.hom g t).symm
    _ = 9 := threeTorsionGeometricFiber_rank K t

end FLT.Mazur.OddWeierstrassParameter

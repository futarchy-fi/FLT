/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAuxiliaryFiniteType
public import FLT.Mazur.SchemeOverProductProperties
public import FLT.Mazur.CyclicHomAuxiliaryScheme
public import FLT.Mazur.OddWeierstrassCyclicHomAuxiliaryScheme

/-!
# Finite type of the full auxiliary and cyclic parameter spaces

The faithful auxiliary factor is paired with the entire cyclic homomorphism
scheme. Finite type therefore includes colliding cyclic sections and does not
require the original cyclic subgroup to be etale.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (n : ℕ) [NeZero n]

/-- The full even-chart cyclic parameter map to the integers. -/
def evenParameterToInt :
    (UniversalWeierstrass.cyclicHomAuxiliaryScheme n).left ⟶ Spec (.of ℤ) :=
  (UniversalWeierstrass.cyclicHomAuxiliaryScheme n).hom ≫ evenCoefficientToInt

/-- The full odd-chart cyclic parameter map to the integers. -/
def oddParameterToInt :
    (OddWeierstrassParameter.cyclicHomAuxiliaryScheme n).left ⟶ Spec (.of ℤ) :=
  (OddWeierstrassParameter.cyclicHomAuxiliaryScheme n).hom ≫ oddCoefficientToInt

/-- Both factors of the even parameter space are locally of finite type. -/
instance evenParameterToInt_locallyOfFiniteType : LocallyOfFiniteType (evenParameterToInt n) := by
  let _ : LocallyOfFiniteType UniversalWeierstrass.levelFour.hom :=
    AuxiliaryLevel.faithfulScheme_locallyOfFiniteType _ _
  unfold evenParameterToInt UniversalWeierstrass.cyclicHomAuxiliaryScheme
  infer_instance

/-- Both factors of the odd parameter space are locally of finite type. -/
instance oddParameterToInt_locallyOfFiniteType : LocallyOfFiniteType (oddParameterToInt n) := by
  let _ : LocallyOfFiniteType OddWeierstrassParameter.levelThree.hom :=
    AuxiliaryLevel.faithfulScheme_locallyOfFiniteType _ _
  unfold oddParameterToInt OddWeierstrassParameter.cyclicHomAuxiliaryScheme
  infer_instance

/-- The complete even parameter map is quasi-compact. -/
instance evenParameterToInt_quasiCompact : QuasiCompact (evenParameterToInt n) := by
  let _ : QuasiCompact UniversalWeierstrass.levelFour.hom :=
    AuxiliaryLevel.faithfulScheme_quasiCompact _ _
  unfold evenParameterToInt UniversalWeierstrass.cyclicHomAuxiliaryScheme
  infer_instance

/-- The complete odd parameter map is quasi-compact. -/
instance oddParameterToInt_quasiCompact : QuasiCompact (oddParameterToInt n) := by
  let _ : QuasiCompact OddWeierstrassParameter.levelThree.hom :=
    AuxiliaryLevel.faithfulScheme_quasiCompact _ _
  unfold oddParameterToInt OddWeierstrassParameter.cyclicHomAuxiliaryScheme
  infer_instance

/-- The even parameter space is Noetherian, including all cyclic marking equations. -/
instance evenParameter_isNoetherian :
    IsNoetherian (UniversalWeierstrass.cyclicHomAuxiliaryScheme n).left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (evenParameterToInt n)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (evenParameterToInt n)

/-- The odd parameter space is Noetherian, including all cyclic marking equations. -/
instance oddParameter_isNoetherian :
    IsNoetherian (OddWeierstrassParameter.cyclicHomAuxiliaryScheme n).left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (oddParameterToInt n)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (oddParameterToInt n)

end FLT.Mazur.CyclicCharacteristicAtlas

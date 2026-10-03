/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateScalarGenerator

/-!
# The negative Tate comparison on cycle representatives

The canonical comparison in degree minus two preserves the underlying
one-chain. In particular the scalar bar class maps to the same group element
in the additive abelianization, without an inverse.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex groupHomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- The degree-minus-two comparison preserves actual one-cycle representatives. -/
theorem tateCocycleClass_negative_two (z : (inhomogeneousChains M).X 1)
    (hz : (inhomogeneousChains M).d 1 0 z = 0)
    (ht : (tateComplex M).d (-2) (-2 + 1) z = 0) :
    ((TateCohomology.isoGroupHomology (-2) 1 (by decide)).app M).hom
      (tateCocycleClass M (-2) z ht) =
      π M 1 ((inhomogeneousChains M).cyclesMk z 0 (by simp) hz) := by
  apply (ModuleCat.mono_iff_injective ((inhomogeneousChains M).homologyι 1)).mp inferInstance
  change (((TateCohomology.isoGroupHomology (-2) 1 (by decide)).app M).hom ≫
    (inhomogeneousChains M).homologyι 1) _ = _
  change (((tateComplexConnectData M).homologyIsoNeg 1 (-2) (by decide)).hom ≫
    (inhomogeneousChains M).homologyι 1) _ = _
  simp only [CochainComplex.ConnectData.homologyIsoNeg, Iso.trans_hom, Iso.symm_hom,
    homologyMapIso_hom]
  simp only [Category.assoc, homologyι_naturality, restrictionHomologyIso_inv_homologyι_assoc]
  simp only [tateCocycleClass, π, ← ConcreteCategory.comp_apply, ← Category.assoc,
    homology_π_ι]
  simp only [Category.assoc, pOpcycles_restrictionOpcyclesIso_inv_assoc]
  simp only [p_opcyclesMap, CochainComplex.ConnectData.restrictionLEIso_hom_f,
    Iso.inv_hom_id_assoc, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  change ((inhomogeneousChains M).pOpcycles 1).hom
    (((tateComplex M).iCycles (-2)).hom
      ((tateComplex M).cyclesMk z (-2 + 1) (by simp) (by exact ht))) =
    (((inhomogeneousChains M).homologyπ 1 ≫
      (inhomogeneousChains M).homologyι 1).hom) _
  rw [homology_π_ι]
  apply congrArg ((inhomogeneousChains M).pOpcycles 1).hom
  exact ((tateComplex M).i_cyclesMk (i := (-2 : ℤ)) z (-2 + 1) (by simp) (by exact ht)).trans
    ((inhomogeneousChains M).i_cyclesMk (i := 1) z 0 (by simp) hz).symm

end LocalClassFieldTheory

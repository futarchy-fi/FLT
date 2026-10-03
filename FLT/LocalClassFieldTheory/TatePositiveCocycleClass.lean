/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateCocycleClass

/-!
# Positive Tate comparison on cocycle representatives

The canonical Mathlib comparison is the identity on positive cochains.
This ties computations in the actual Tate complex to ordinary cochain cups.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex groupCohomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- The positive Tate comparison sends each cocycle to its ordinary cohomology class. -/
theorem tateCocycleClass_positive (n : ℕ) [NeZero n] (z : (Fin n → G) → M)
    (hz : (inhomogeneousCochains M).d n (n + 1) z = 0)
    (ht : (tateComplex M).d (n : ℤ) (n + 1) z = 0) :
    ((TateCohomology.isoGroupCohomology n).app M).hom
      (tateCocycleClass M n z ht) =
      π M n ((inhomogeneousCochains M).cyclesMk z (n + 1) (by simp) hz) := by
  apply (ModuleCat.mono_iff_injective ((inhomogeneousCochains M).homologyι n)).mp inferInstance
  change (((TateCohomology.isoGroupCohomology n).app M).hom ≫
    (inhomogeneousCochains M).homologyι n) _ = _
  change (((tateComplexConnectData M).homologyIsoPos n n rfl).hom ≫
    (inhomogeneousCochains M).homologyι n) _ = _
  simp only [CochainComplex.ConnectData.homologyIsoPos, Iso.trans_hom, Iso.symm_hom,
    homologyMapIso_hom]
  simp only [Category.assoc, homologyι_naturality, restrictionHomologyIso_inv_homologyι_assoc]
  simp only [tateCocycleClass, π, ← ConcreteCategory.comp_apply, ← Category.assoc,
    homology_π_ι]
  simp only [Category.assoc, pOpcycles_restrictionOpcyclesIso_inv_assoc]
  simp only [p_opcyclesMap, CochainComplex.ConnectData.restrictionGEIso_hom_f,
    Iso.inv_hom_id_assoc, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  change ((inhomogeneousCochains M).pOpcycles n).hom
    (((tateComplex M).iCycles n).hom ((tateComplex M).cyclesMk z (n + 1) (by simp) ht)) =
    (((inhomogeneousCochains M).homologyπ n ≫
      (inhomogeneousCochains M).homologyι n).hom) _
  rw [homology_π_ι]
  apply congrArg ((inhomogeneousCochains M).pOpcycles n).hom
  exact ((tateComplex M).i_cyclesMk (i := (n : ℤ)) z (n + 1) (by simp) ht).trans
    ((inhomogeneousCochains M).i_cyclesMk (i := n) z (n + 1) (by simp) hz).symm

/-- A nonnegative ordinary cocycle defines a class in the actual Tate complex. -/
def tateClassOfCochain (n : ℕ) (z : (Fin n → G) → M)
    (hz : inhomogeneousCochains.d M n z = 0) : tateCohomology M n :=
  tateCocycleClass M n z (by
    rw [tateComplex_d_ofNat, inhomogeneousCochains.d_def]
    exact hz)

/-- The ordinary representative is preserved by the positive Tate comparison. -/
theorem tateClassOfCochain_positive (n : ℕ) [NeZero n] (z : (Fin n → G) → M)
    (hz : inhomogeneousCochains.d M n z = 0) :
    ((TateCohomology.isoGroupCohomology n).app M).hom (tateClassOfCochain M n z hz) =
      π M n (cocyclesMk z hz) :=
  tateCocycleClass_positive M n z (by rw [inhomogeneousCochains.d_def]; exact hz) _

end LocalClassFieldTheory

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateCocycleClass

/-!
# Arithmetic and boundaries of Tate cocycle classes

Scalar multiplication and the boundary criterion are proved on the actual
integer-indexed complex, including the norm differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G) (n : ℤ)

/-- Scalar multiplication of representatives agrees with scalar multiplication of Tate classes. -/
theorem tateCocycleClass_smul (r : k) (z : (tateComplex M).X n)
    (hz : (tateComplex M).d n (n + 1) z = 0)
    (hrz : (tateComplex M).d n (n + 1) (r • z) = 0) :
    tateCocycleClass M n (r • z) hrz = r • tateCocycleClass M n z hz := by
  let cz : (tateComplex M).cycles n := (tateComplex M).cyclesMk z (n + 1) (by simp) hz
  let crz : (tateComplex M).cycles n :=
    (tateComplex M).cyclesMk (r • z) (n + 1) (by simp) hrz
  have hc : crz = r • cz := by
    apply (ModuleCat.mono_iff_injective ((tateComplex M).iCycles n)).mp inferInstance
    calc
      _ = r • z := (tateComplex M).i_cyclesMk _ _ _ _
      _ = r • ((tateComplex M).iCycles n).hom cz :=
        congrArg (r • ·) ((tateComplex M).i_cyclesMk z (n + 1) (by simp) hz).symm
      _ = _ := (((tateComplex M).iCycles n).hom.map_smul r _).symm
  exact (congrArg ((tateComplex M).homologyπ n).hom hc).trans
    (((tateComplex M).homologyπ n).hom.map_smul r _)

/-- Integer multiples of representatives agree with integer multiples of Tate classes. -/
theorem tateCocycleClass_zsmul (r : ℤ) (z : (tateComplex M).X n)
    (hz : (tateComplex M).d n (n + 1) z = 0)
    (hrz : (tateComplex M).d n (n + 1) (r • z) = 0) :
    tateCocycleClass M n (r • z) hrz = r • tateCocycleClass M n z hz := by
  let cz : (tateComplex M).cycles n := (tateComplex M).cyclesMk z (n + 1) (by simp) hz
  let crz : (tateComplex M).cycles n :=
    (tateComplex M).cyclesMk (r • z) (n + 1) (by simp) hrz
  have hc : crz = r • cz := by
    apply (ModuleCat.mono_iff_injective ((tateComplex M).iCycles n)).mp inferInstance
    calc
      _ = r • z := (tateComplex M).i_cyclesMk _ _ _ _
      _ = r • ((tateComplex M).iCycles n).hom cz :=
        congrArg (r • ·) ((tateComplex M).i_cyclesMk z (n + 1) (by simp) hz).symm
      _ = _ := (map_zsmul ((tateComplex M).iCycles n).hom r cz).symm
  exact (congrArg ((tateComplex M).homologyπ n).hom hc).trans
    (map_zsmul ((tateComplex M).homologyπ n).hom r cz)

/-- A Tate cocycle is zero in cohomology exactly when it is a boundary in the same complex. -/
theorem tateCocycleClass_eq_zero_iff (z : (tateComplex M).X n)
    (hz : (tateComplex M).d n (n + 1) z = 0) :
    tateCocycleClass M n z hz = 0 ↔
      ∃ b : (tateComplex M).X (n - 1), (tateComplex M).d (n - 1) n b = z := by
  have he : (tateComplex M).homologyι n (tateCocycleClass M n z hz) =
      (tateComplex M).pOpcycles n z := by
    change (((tateComplex M).homologyπ n ≫ (tateComplex M).homologyι n).hom)
      ((tateComplex M).cyclesMk z (n + 1) (by simp) hz) = _
    rw [homology_π_ι]
    exact congrArg ((tateComplex M).pOpcycles n)
      ((tateComplex M).i_cyclesMk z (n + 1) (by simp) hz)
  rw [← (ModuleCat.mono_iff_injective ((tateComplex M).homologyι n)).mp
    inferInstance |>.eq_iff, map_zero, he]
  have h := ((tateComplex M).sc n).moduleCat_pOpcycles_eq_zero_iff z
  change (tateComplex M).pOpcycles n z = 0 ↔ ∃ b : (tateComplex M).X ((ComplexShape.up ℤ).prev n),
    (tateComplex M).d ((ComplexShape.up ℤ).prev n) n b = z at h
  rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (n - 1) n by
    change n - 1 + 1 = n
    omega)] at h
  exact h

end LocalClassFieldTheory

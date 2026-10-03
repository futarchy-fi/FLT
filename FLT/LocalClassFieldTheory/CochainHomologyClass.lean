/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Representatives for cohomology of complexes of modules

The categorical homology class of a cocycle vanishes exactly when that cocycle
is a boundary. Using the complex shape's predecessor also covers degree zero.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable {k : Type u} [CommRing k]
  (K : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ)

/-- A cochain map sends cycles to cycles. -/
theorem cochainMap_cycle {L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)
    (m : ℕ) (z : K.X n) (hz : (K.d n m).hom z = 0) :
    (L.d n m).hom ((f.f n).hom z) = 0 := by
  have h := congrArg (fun g => g.hom z) (f.comm n m).symm
  change (f.f m).hom ((K.d n m).hom z) = _ at h
  simpa only [hz, map_zero, ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

/-- The cycle constructor retains the original cochain. -/
theorem cochainCyclesMk_val (z : K.X n)
    (hz : (K.d n ((ComplexShape.up ℕ).next n)).hom z = 0) :
    (K.iCycles n).hom (K.cyclesMk z _ rfl hz) = z :=
  K.i_cyclesMk z _ rfl hz

/-- The categorical cohomology class represented by an actual cocycle. -/
def cochainHomologyClass (z : K.X n)
    (hz : (K.d n ((ComplexShape.up ℕ).next n)).hom z = 0) : K.homology n :=
  (K.homologyπ n).hom (K.cyclesMk z _ rfl hz)

/-- Every cohomology class has a cocycle representative. -/
theorem cochainHomologyClass_surjective (x : K.homology n) :
    ∃ (z : K.X n) (hz : (K.d n ((ComplexShape.up ℕ).next n)).hom z = 0),
      cochainHomologyClass K n z hz = x := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance x
  have hz : (K.d n ((ComplexShape.up ℕ).next n)).hom ((K.iCycles n).hom y) = 0 :=
    congrArg (fun f => f.hom y) (K.iCycles_d n ((ComplexShape.up ℕ).next n))
  refine ⟨(K.iCycles n).hom y, hz, congrArg (K.homologyπ n).hom ?_⟩
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  exact K.i_cyclesMk _ _ rfl _

/-- A cocycle class is zero precisely when it is a boundary in the same complex. -/
theorem cochainHomologyClass_eq_zero_iff (z : K.X n)
    (hz : (K.d n ((ComplexShape.up ℕ).next n)).hom z = 0) :
    cochainHomologyClass K n z hz = 0 ↔
      ∃ b : K.X ((ComplexShape.up ℕ).prev n),
        (K.d ((ComplexShape.up ℕ).prev n) n).hom b = z := by
  have he : (K.homologyι n).hom (cochainHomologyClass K n z hz) =
      (K.pOpcycles n).hom z := by
    change ((K.homologyπ n ≫ K.homologyι n).hom) (K.cyclesMk z _ rfl hz) = _
    rw [K.homology_π_ι]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cochainCyclesMk_val]
  rw [← (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance |>.eq_iff,
    map_zero, he]
  exact (K.sc n).moduleCat_pOpcycles_eq_zero_iff z

/-- Taking representatives commutes with the induced cohomology map. -/
theorem cochainHomologyClass_map {L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)
    (z : K.X n) (hz : (K.d n ((ComplexShape.up ℕ).next n)).hom z = 0)
    (hfz : (L.d n ((ComplexShape.up ℕ).next n)).hom ((f.f n).hom z) = 0) :
    (homologyMap f n).hom (cochainHomologyClass K n z hz) =
      cochainHomologyClass L n ((f.f n).hom z) hfz := by
  change ((K.homologyπ n ≫ homologyMap f n).hom) (K.cyclesMk z _ rfl hz) = _
  rw [homologyπ_naturality]
  apply congrArg (L.homologyπ n).hom
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  change ((cyclesMap f n ≫ L.iCycles n).hom) (K.cyclesMk z _ rfl hz) = _
  rw [cyclesMap_i]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cochainCyclesMk_val]

end LocalClassFieldTheory

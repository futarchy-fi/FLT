/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalHenselian
public import FLT.GroupScheme.LocalPolynomialObstruction
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.UniformizerMinpoly
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.UnramifiedSubalgebra
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Eisenstein presentations over an unramified coefficient ring

Every finite three-adic ring of integers contains a finite unramified DVR
with the same residue field. Over this coefficient ring, any uniformizer
has an Eisenstein minimal polynomial and generates the full ring of integers.
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- A finite three-adic integer ring has an Eisenstein power-basis presentation
over an unramified coefficient DVR, with degree equal to its ramification index. -/
theorem existsThreeAdicEisensteinPresentation :
    ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsDiscreteValuationRing C)
      (_ : Algebra ℤ_[3] C) (_ : Module.Finite ℤ_[3] C) (_ : Algebra C (ThreeAdicIntegers L))
      (_ : IsScalarTower ℤ_[3] C (ThreeAdicIntegers L))
      (_ : FaithfulSMul C (ThreeAdicIntegers L)) (_ : FaithfulSMul ℤ_[3] C)
      (_ : Algebra.FormallyUnramified ℤ_[3] C) (pb : PowerBasis C (ThreeAdicIntegers L)),
      Irreducible (3 : C) ∧ Irreducible pb.gen ∧
        (minpoly C pb.gen).IsEisensteinAt (maximalIdeal C) ∧
        pb.dim = threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) ∧
        ∀ s : ThreeAdicIntegers L, ∃ c : C,
          residue (ThreeAdicIntegers L) (algebraMap C (ThreeAdicIntegers L) c) =
            residue (ThreeAdicIntegers L) s := by
  let A := ThreeAdicIntegers L
  let instFiniteResidue : Finite (ResidueField ℤ_[3]) :=
    Finite.of_equiv (ZMod 3) PadicInt.residueField.symm.toEquiv
  have h3 : Irreducible (3 : ℤ_[3]) := by
    apply (irreducible_iff_uniformizer _).mpr
    simpa using PadicInt.maximalIdeal_eq_span_p (p := 3)
  obtain ⟨C, instRing, instDomain, instDvr, instAlgR, instFinite, instAlgC,
    instTower, hinj, h3C, hres⟩ := existsUnramifiedCoefficientRing (S := A) h3
  let instFaithful : FaithfulSMul C A :=
    (faithfulSMul_iff_algebraMap_injective C A).mpr hinj
  have hinjR : Function.Injective (algebraMap ℤ_[3] C) := by
    intro x y h
    apply FaithfulSMul.algebraMap_injective ℤ_[3] A
    rw [IsScalarTower.algebraMap_apply ℤ_[3] C A,
      IsScalarTower.algebraMap_apply ℤ_[3] C A, h]
  let instFaithfulR : FaithfulSMul ℤ_[3] C :=
    (faithfulSMul_iff_algebraMap_injective ℤ_[3] C).mpr hinjR
  have h3C' : Irreducible (3 : C) := by simpa only [map_ofNat] using h3C
  let instFiniteC : Module.Finite C A := .of_restrictScalars_finite ℤ_[3] C A
  let instResidueFinite : FiniteDimensional (ResidueField ℤ_[3]) (ResidueField C) :=
    IsLocalRing.ResidueField.finite_of_module_finite
  let instResidueAlgebraic : Algebra.IsAlgebraic (ResidueField ℤ_[3]) (ResidueField C) :=
    Algebra.IsAlgebraic.of_finite _ _
  let instResiduePerfect : PerfectField (ResidueField ℤ_[3]) := PerfectField.ofFinite
  let instResidueSeparable : Algebra.IsSeparable (ResidueField ℤ_[3]) (ResidueField C) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  let instUnramified : Algebra.FormallyUnramified ℤ_[3] C :=
    Algebra.FormallyUnramified.iff_map_maximalIdeal_eq.mpr ⟨inferInstance, by
      rw [h3.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
      exact h3C.maximalIdeal_eq.symm⟩
  obtain ⟨y, hy⟩ := exists_irreducible A
  obtain ⟨pb, hpb⟩ := existsUniformizerPowerBasis hres hy
  have hgen : Irreducible pb.gen := hpb ▸ hy
  refine ⟨C, instRing, instDomain, instDvr, instAlgR, instFinite, instAlgC,
    instTower, instFaithful, instFaithfulR, instUnramified, pb, h3C', hgen,
    pb.minpolyEisensteinOfUniformizer hgen hres, ?_, hres⟩
  have hv := finrankEqAddValMapUniformizer hres h3C'
  rw [pb.finrank, map_ofNat, threeAdicAddValEqIdealOrder] at hv
  · exact ENat.natCast_inj.mp hv
  · let instCharZero : CharZero A := Algebra.charZero_of_charZero ℤ_[3] A
    norm_num

end ThreeAdicPlan

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.Categories
public import FLT.LocalClassFieldTheory.FiniteDvrComplete
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.Eisenstein

/-!
# Ramified coefficient objects

A monic Eisenstein polynomial over a complete DVR with finite residue field
constructs a domain in the deformation category with the same residue field.
This constructs coefficients only, not a representation over them.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IsLocalRing
namespace Deformation.EisensteinCoefficients

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  (P : R[X]) [hE : Fact (P.IsEisensteinAt (maximalIdeal R))]
  [hM : Fact P.Monic] [hD : Fact (0 < P.natDegree)]

local notation "hP" => hE.out
local notation "hm" => hM.out
local notation "hd" => hD.out

local instance : IsDomain (AdjoinRoot P) :=
  AdjoinRoot.isDomain_of_prime (hE.out.irreducible inferInstance hM.out.isPrimitive hd).prime

local instance : Module.Finite R (AdjoinRoot P) := hM.out.finite_adjoinRoot

local instance : FaithfulSMul R (AdjoinRoot P) :=
  (faithfulSMul_iff_algebraMap_injective R (AdjoinRoot P)).mpr
    (AdjoinRoot.of.injective_of_monic_of_degree_pos hm (natDegree_pos_iff_degree_pos.mp hd))

local instance : IsDiscreteValuationRing (AdjoinRoot P) :=
  (AdjoinRoot.isDiscreteValuationRingOfEisenstein hP hm hd).1

omit [Finite (ResidueField R)] [IsAdicComplete (maximalIdeal R) R] in
/-- Reduction of a polynomial in the root is reduction of its constant coefficient. -/
theorem residue_mk (f : R[X]) :
    residue (AdjoinRoot P) (AdjoinRoot.mk P f) =
      residue (AdjoinRoot P) (algebraMap R (AdjoinRoot P) (f.coeff 0)) := by
  apply sub_eq_zero.mp
  rw [← map_sub, residue_eq_zero_iff]
  rw [AdjoinRoot.maximalIdealEqSpanRootOfEisenstein hP hm hd
    (maximalIdeal (AdjoinRoot P)) inferInstance]
  apply Ideal.mem_span_singleton.mpr
  simpa using map_dvd (aeval (AdjoinRoot.root P)) (X_dvd_sub_C (p := f))

local instance : IsResidueAlgebra R (AdjoinRoot P) where
  isSurjective' := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective (R := AdjoinRoot P) x
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
    exact ⟨f.coeff 0, (residue_mk R P f).symm⟩

local instance : Finite (ResidueField (AdjoinRoot P)) :=
  Finite.of_surjective (IsResidueAlgebra.algEquiv R (AdjoinRoot P))
    (IsResidueAlgebra.algEquiv R (AdjoinRoot P)).surjective

local instance : IsAdicComplete (maximalIdeal (AdjoinRoot P)) (AdjoinRoot P) :=
  LocalClassFieldTheory.finiteDvr_complete R (AdjoinRoot P)

/-- The constructed ramified order with its maximal-ideal topology and original scalars. -/
def object : ProartinianCat R where
  carrier := AdjoinRoot P
  topologicalSpace := (ProartinianCat.self (𝓞 := AdjoinRoot P)).topologicalSpace
  isLocalProartinianAlgebra :=
    letI : TopologicalSpace (AdjoinRoot P) :=
      (ProartinianCat.self (𝓞 := AdjoinRoot P)).topologicalSpace
    letI : IsLocalProartinianAlgebra (AdjoinRoot P) (AdjoinRoot P) :=
      (ProartinianCat.self (𝓞 := AdjoinRoot P)).isLocalProartinianAlgebra
    ⟨⟩

/-- The target is a domain, rather than just a nonzero proartinian ring. -/
theorem object_isDomain : IsDomain (object R P) :=
  inferInstanceAs (IsDomain (AdjoinRoot P))

/-- The original coefficients embed into the ramified target. -/
theorem object_injective : Function.Injective (algebraMap R (object R P)) :=
  FaithfulSMul.algebraMap_injective R (AdjoinRoot P)

/-- Characteristic zero is preserved in this explicit target. -/
theorem object_charZero [CharZero R] : CharZero (object R P) :=
  charZero_of_injective_algebraMap (object_injective R P)

/-- The extension is finite over its coefficient base. -/
theorem object_finite : Module.Finite R (object R P) := hM.out.finite_adjoinRoot

end Deformation.EisensteinCoefficients

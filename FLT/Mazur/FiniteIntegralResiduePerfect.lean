/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.FieldTheory.Perfect

/-!
# Perfect residue fields after finite integral extension and localization

A maximal residue field of a finite algebra is finite over the original
local residue field. The conclusion transfers to any realization of the
localization, including the subalgebra in the prescribed generic field.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteIntegralResiduePerfect
open IsLocalRing
variable (R C : Type) [CommRing R] [IsLocalRing R] [CommRing C]
  [Algebra R C] [Module.Finite R C] [PerfectField (ResidueField R)]
  (Q : Ideal C) [Q.IsMaximal]

include R in
/-- Maximal residue fields of a finite algebra over the original local ring are perfect. -/
theorem residueField_perfect : PerfectField Q.ResidueField := by
  let _ : Module.Finite R Q.ResidueField := Module.Finite.trans C Q.ResidueField
  let _ : Algebra (ResidueField R) Q.ResidueField := inferInstance
  exact Algebra.IsAlgebraic.perfectField (ResidueField R)

include R in
/-- Any realization of the same localization has the same perfect residue field. -/
theorem localization_perfect (S : Type) [CommRing S] [Algebra C S]
    [IsLocalization.AtPrime S Q] [IsLocalRing S] : PerfectField (ResidueField S) := by
  let _ := residueField_perfect R C Q
  exact PerfectField.of_ringEquiv
    (ResidueField.mapEquiv (IsLocalization.algEquiv Q.primeCompl
      (Localization.AtPrime Q) S).toRingEquiv)

end FLT.Mazur.FiniteIntegralResiduePerfect

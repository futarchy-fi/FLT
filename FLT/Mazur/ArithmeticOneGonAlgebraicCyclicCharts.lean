/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAlgebraicFamily
public import FLT.Mazur.GeneralizedCurveUnrestrictedChartCoverage

/-!
# Finite-presentation cyclic charts with a varying arithmetic curve

The unrestricted closed cyclic chart and its ample open now lie over a fixed
finite-presentation integral base. Their families vary with the degeneration
parameter and retain nonetale cyclic subgroups and both auxiliary markings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonParameter
open CyclicBoundaryParameter

/-- The algebraic degeneration base is Noetherian. -/
instance parameterBase_isNoetherian : IsNoetherian parameterBase := inferInstance

/-- The algebraic parameter base is quasi-compact over the integers. -/
instance toIntegers_quasiCompact : QuasiCompact toIntegers := by
  unfold toIntegers
  infer_instance

/-- The algebraic parameter base is separated over the integers. -/
instance toIntegers_separated : IsSeparated toIntegers := by
  unfold toIntegers
  infer_instance

variable (n : ℕ) [NeZero n]

/-- The full cyclic chart with a varying degeneration parameter. -/
abbrev closedChart : Scheme := unrestrictedMultiplicationLocus universalCurve n

/-- The ample part of the varying cyclic chart. -/
abbrev ampleChart : Scheme := (unrestrictedAmpleOpen universalCurve n).toScheme

/-- The closed chart's original integral structure map. -/
def closedChartToIntegers : closedChart n ⟶ Spec (.of ℤ) :=
  unrestrictedLocusBase universalCurve n ≫ toIntegers

/-- The ample chart's original integral structure map. -/
def ampleChartToIntegers : ampleChart n ⟶ Spec (.of ℤ) :=
  unrestrictedAmpleBase universalCurve n ≫ toIntegers

/-- The closed chart is locally finitely presented over the integers. -/
instance closedChartToIntegers_lfp : LocallyOfFinitePresentation (closedChartToIntegers n) :=
  inferInstanceAs (LocallyOfFinitePresentation (_ ≫ toIntegers))

/-- The closed chart is quasi-compact over the integers. -/
instance closedChartToIntegers_quasiCompact : QuasiCompact (closedChartToIntegers n) :=
  inferInstanceAs (QuasiCompact (_ ≫ toIntegers))

/-- The closed chart is separated over the integers. -/
instance closedChartToIntegers_separated : IsSeparated (closedChartToIntegers n) :=
  inferInstanceAs (IsSeparated (_ ≫ toIntegers))

/-- The ample chart is locally finitely presented over the integers. -/
instance ampleChartToIntegers_lfp : LocallyOfFinitePresentation (ampleChartToIntegers n) :=
  inferInstanceAs (LocallyOfFinitePresentation (_ ≫ toIntegers))

/-- The ample chart is quasi-compact over the integers. -/
instance ampleChartToIntegers_quasiCompact : QuasiCompact (ampleChartToIntegers n) :=
  inferInstanceAs (QuasiCompact (_ ≫ toIntegers))

/-- The ample chart is separated over the integers. -/
instance ampleChartToIntegers_separated : IsSeparated (ampleChartToIntegers n) :=
  inferInstanceAs (IsSeparated (_ ≫ toIntegers))

end FLT.Mazur.ArithmeticOneGonParameter

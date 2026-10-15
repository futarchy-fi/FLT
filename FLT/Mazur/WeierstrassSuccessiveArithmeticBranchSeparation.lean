/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNodeChartDisjoint
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorBranches

/-!
# Separation of the actual arithmetic tensor branches

The original small and opposite branches are disjoint at every quotient
order. Any pair of unequal Boolean labels has empty full scheme intersection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "C" => arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6

/-- Both complete arithmetic polygon charts have disjoint images in the original equation. -/
theorem arithmeticNodeCharts_disjoint :
    Disjoint (Set.range (arithmeticNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6))
      (Set.range (arithmeticOppositeNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6)) :=
  nilpotentPolygonCharts_disjoint (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6)

/-- The full original tensor branches inherit separation through their actual base change. -/
theorem arithmeticTensorBranches_disjoint :
    Disjoint (Set.range (C false)) (Set.range (C true)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  let e := PrimeSpectrum.comapEquiv (baseChangeEquiv W s π b3 b4 b6 Q).toRingEquiv
  have he := e.symm.injective hy
  exact Set.disjoint_left.mp (arithmeticNodeCharts_disjoint π m W s b3 b4 b6 ha hs h2 h3 h4 h6)
    ⟨x, rfl⟩ ⟨y, he⟩

/-- Any two different constructed labels have disjoint complete arithmetic tensor images. -/
theorem arithmeticTensorBranchChart_disjoint (a b : Bool) (hab : a ≠ b) :
    Disjoint (Set.range (C a)) (Set.range (C b)) := by
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact arithmeticTensorBranches_disjoint π m W s b3 b4 b6 ha hs h2 h3 h4 h6
  · exact (arithmeticTensorBranches_disjoint π m W s b3 b4 b6 ha hs h2 h3 h4 h6).symm
  · exact (hab rfl).elim

/-- The entire intersection of distinct labels is the empty scheme at every quotient order. -/
theorem arithmeticTensorBranchChart_isPullback_empty (a b : Bool) (hab : a ≠ b) :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (C a) (C b) := by
  let _ := Scheme.isEmpty_pullback (C a) (C b)
    (arithmeticTensorBranchChart_disjoint π m W s b3 b4 b6 ha hs h2 h3 h4 h6 a b hab)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (C a) (C b))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassSuccessiveX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalComponentLifting
public import FLT.GroupScheme.PadicConnectedComponents

/-! # Connected finite-flat algebra factors of the original rational-place models

This is an algebra decomposition; the Hopf quotient and the etale quotient
require further constructions and are not asserted here.
-/

@[expose] public noncomputable section
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian

namespace FF

variable {p : ℕ} [Fact p.Prime]
  (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)

/-- The connected components are indexed by the maximal ideals of the special fibre. -/
abbrev RationalComponentIndex := MaximalSpectrum (X.CoordinateRing ⧸ rationalSpecialIdeal p
  X.CoordinateRing)

instance rationalComponentIndexFinite : Finite X.RationalComponentIndex := inferInstanceAs
  (Finite (MaximalSpectrum _))

/-- The idempotent defining an integral connected component. -/
def rationalComponentIdempotent (m : X.RationalComponentIndex) : X.CoordinateRing :=
  componentIdempotent (rationalSpecialIdeal p X.CoordinateRing) m

/-- The coordinate algebra of a connected component, as an actual integral quotient. -/
abbrev RationalComponentAlgebra (m : X.RationalComponentIndex) :=
  X.CoordinateRing ⧸ Ideal.span {1 - X.rationalComponentIdempotent m}

/-- Every component algebra is finite over `O`. -/
instance rationalComponentFinite (m : X.RationalComponentIndex) : Module.Finite O
  (X.RationalComponentAlgebra m) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap
    Ideal.Quotient.mk_surjective

/-- Every component algebra is flat over `O`. -/
instance rationalComponentFlat (m : X.RationalComponentIndex) : Module.Flat O
  (X.RationalComponentAlgebra m) :=
  flat_quotient_complement_idempotent
    (componentIdempotent_isIdempotent (rationalSpecialIdeal p X.CoordinateRing) m)

/-- A component has no nontrivial idempotents: its affine spectrum is connected. -/
theorem rationalComponentAlgebra_idempotent_trivial (m : X.RationalComponentIndex)
    (d : X.RationalComponentAlgebra m) (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 :=
  componentFactor_idempotent_trivial (rationalSpecialIdeal p X.CoordinateRing) m d hd

/-- Every finite-flat model over `O` has an integral algebra decomposition
into connected finite-flat component algebras. No generic section is required. -/
def rationalComponentEquiv : X.CoordinateRing ≃ₐ[O] Π m : X.RationalComponentIndex,
    X.RationalComponentAlgebra m := primitiveComponentEquiv (rationalSpecialIdeal p
      X.CoordinateRing)

/-- Component idempotents are nonzero, so the components are not empty. -/
theorem rationalComponentIdempotent_ne_zero (m : X.RationalComponentIndex) :
    X.rationalComponentIdempotent m ≠ 0 := by
  let : Field ((X.CoordinateRing ⧸ rationalSpecialIdeal p X.CoordinateRing) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  intro h
  have hh := congrArg (fun x ↦ componentResidueMap (rationalSpecialIdeal p X.CoordinateRing) x m) h
  simp [rationalComponentIdempotent] at hh

instance rationalComponentNontrivial (m : X.RationalComponentIndex) : Nontrivial
  (X.RationalComponentAlgebra m) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  let e := X.rationalComponentIdempotent m
  have he : IsIdempotentElem e :=
    componentIdempotent_isIdempotent (rationalSpecialIdeal p X.CoordinateRing) m
  have hm : e ∈ Ideal.span {1 - e} := by rw [h]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
  have hh := congrArg (e * ·) ha
  rw [← mul_assoc, he.mul_one_sub_self, zero_mul, he.eq] at hh
  exact X.rationalComponentIdempotent_ne_zero m hh

end FF
end ThreeAdicPlan

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HenselianComponents
public import FLT.GroupScheme.PadicComponentLifting

/-!
# Connected algebra components of finite-flat three-adic models

The special fibre is Artinian. Its maximal ideals canonically index a product
decomposition of the integral coordinate ring into connected finite-flat
algebras. This is the component decomposition of the underlying affine scheme;
the quotient factors are not yet equipped with Hopf structures.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- The special fibre of a finite three-adic algebra is Artinian. -/
theorem threeAdicSpecialFiber_artinian (A : Type*) [CommRing A] [Algebra ℤ_[3] A]
    [Module.Finite ℤ_[3] A] : IsArtinianRing (A ⧸ threeAdicSpecialIdeal A) := by
  let k := IsLocalRing.ResidueField ℤ_[3]
  let B := A ⧸ threeAdicSpecialIdeal A
  let : Algebra k B := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower ℤ_[3] k B := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite k B := Module.Finite.of_restrictScalars_finite ℤ_[3] k B
  exact IsArtinianRing.of_finite k B

attribute [local instance] threeAdicFiniteFlat_henselian threeAdicSpecialFiber_artinian

/-- Quotienting by a complementary idempotent preserves module flatness. -/
theorem flat_quotient_complement_idempotent {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] {e : A} (he : IsIdempotentElem e) :
    Module.Flat R (A ⧸ Ideal.span {1 - e}) := by
  let E := AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he
    (sub_add_cancel 1 e) he.one_sub_mul_self
  let i := E.symm.toLinearMap.comp
    (LinearMap.inl R (A ⧸ Ideal.span {1 - e}) (A ⧸ Ideal.span {e}))
  let r := (LinearMap.fst R (A ⧸ Ideal.span {1 - e}) (A ⧸ Ideal.span {e})).comp E.toLinearMap
  apply Module.Flat.of_retract i r
  apply LinearMap.ext
  intro x
  change (E (E.symm (x, 0))).1 = x
  rw [E.apply_symm_apply]

namespace FF

variable (X : FF ℤ_[3] ℚ_[3])

/-- The connected components are indexed by the maximal ideals of the special fibre. -/
abbrev ComponentIndex := MaximalSpectrum (X.CoordinateRing ⧸ threeAdicSpecialIdeal X.CoordinateRing)

instance : Finite X.ComponentIndex := inferInstanceAs (Finite (MaximalSpectrum _))

/-- The idempotent defining an integral connected component. -/
def connectedComponentIdempotent (m : X.ComponentIndex) : X.CoordinateRing :=
  componentIdempotent (threeAdicSpecialIdeal X.CoordinateRing) m

/-- The coordinate algebra of a connected component, as an actual integral quotient. -/
abbrev ComponentAlgebra (m : X.ComponentIndex) :=
  X.CoordinateRing ⧸ Ideal.span {1 - X.connectedComponentIdempotent m}

/-- Every component algebra is finite over `ℤ_[3]`. -/
instance (m : X.ComponentIndex) : Module.Finite ℤ_[3] (X.ComponentAlgebra m) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[3] _).toLinearMap
    Ideal.Quotient.mk_surjective

/-- Every component algebra is flat over `ℤ_[3]`. -/
instance (m : X.ComponentIndex) : Module.Flat ℤ_[3] (X.ComponentAlgebra m) :=
  flat_quotient_complement_idempotent
    (componentIdempotent_isIdempotent (threeAdicSpecialIdeal X.CoordinateRing) m)

/-- A component has no nontrivial idempotents: its affine spectrum is connected. -/
theorem componentAlgebra_idempotent_trivial (m : X.ComponentIndex)
    (d : X.ComponentAlgebra m) (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 :=
  componentFactor_idempotent_trivial (threeAdicSpecialIdeal X.CoordinateRing) m d hd

/-- Every finite-flat model over `ℤ_[3]` has an integral algebra decomposition
into connected finite-flat component algebras. No generic section is required. -/
def connectedComponentEquiv : X.CoordinateRing ≃ₐ[ℤ_[3]] Π m : X.ComponentIndex,
    X.ComponentAlgebra m := primitiveComponentEquiv (threeAdicSpecialIdeal X.CoordinateRing)

/-- Component idempotents are nonzero, so the components are not empty. -/
theorem connectedComponentIdempotent_ne_zero (m : X.ComponentIndex) :
    X.connectedComponentIdempotent m ≠ 0 := by
  let : Field ((X.CoordinateRing ⧸ threeAdicSpecialIdeal X.CoordinateRing) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  intro h
  have hh := congrArg (fun x ↦ componentResidueMap (threeAdicSpecialIdeal X.CoordinateRing) x m) h
  simp [connectedComponentIdempotent] at hh

instance (m : X.ComponentIndex) : Nontrivial (X.ComponentAlgebra m) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  let e := X.connectedComponentIdempotent m
  have he : IsIdempotentElem e :=
    componentIdempotent_isIdempotent (threeAdicSpecialIdeal X.CoordinateRing) m
  have hm : e ∈ Ideal.span {1 - e} := by rw [h]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
  have hh := congrArg (e * ·) ha
  rw [← mul_assoc, he.mul_one_sub_self, zero_mul, he.eq] at hh
  exact X.connectedComponentIdempotent_ne_zero m hh

/-- The integral counit singles out exactly one connected component. -/
theorem existsUnique_identityComponent : ∃! m : X.ComponentIndex,
    Coalgebra.counit (R := ℤ_[3]) (X.connectedComponentIdempotent m) = 1 := by
  classical
  let : Fintype X.ComponentIndex := Fintype.ofFinite _
  let ε := Bialgebra.counitAlgHom ℤ_[3] X.CoordinateRing
  have hc := (componentIdempotent_complete (threeAdicSpecialIdeal X.CoordinateRing)).map
    ε.toRingHom
  have hex : ∃ m : X.ComponentIndex, ε (X.connectedComponentIdempotent m) = 1 := by
    by_contra h
    push Not at h
    have hz (m : X.ComponentIndex) : ε (X.connectedComponentIdempotent m) = 0 :=
      (IsIdempotentElem.iff_eq_zero_or_one.mp (hc.idem m)).resolve_right (h m)
    have hs := hc.complete
    change ∑ m, ε (X.connectedComponentIdempotent m) = 1 at hs
    simp only [hz, Finset.sum_const_zero] at hs
    exact zero_ne_one hs
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, hm, fun n hn ↦ ?_⟩
  by_contra hnm
  have hh := hc.ortho hnm
  change ε (X.connectedComponentIdempotent n) * ε (X.connectedComponentIdempotent m) = 0 at hh
  rw [show ε (X.connectedComponentIdempotent n) = 1 from hn, hm, one_mul] at hh
  exact one_ne_zero hh

/-- The component containing the identity section of the group scheme. -/
def identityComponentIndex : X.ComponentIndex := X.existsUnique_identityComponent.choose

/-- The identity-component idempotent has counit one. -/
@[simp] theorem counit_identityComponentIdempotent :
    Coalgebra.counit (R := ℤ_[3]) (X.connectedComponentIdempotent X.identityComponentIndex) = 1 :=
  X.existsUnique_identityComponent.choose_spec.1

/-- The identity section factors through the connected component selected by the counit. -/
def identityComponentCounit : X.ComponentAlgebra X.identityComponentIndex →ₐ[ℤ_[3]] ℤ_[3] :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom ℤ_[3] X.CoordinateRing) (by
    change Ideal.span {1 - X.connectedComponentIdempotent X.identityComponentIndex} ≤
      RingHom.ker (Bialgebra.counitAlgHom ℤ_[3] X.CoordinateRing).toRingHom
    apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change (Bialgebra.counitAlgHom ℤ_[3] X.CoordinateRing)
      (1 - X.connectedComponentIdempotent X.identityComponentIndex) = 0
    rw [map_sub, map_one, Bialgebra.counitAlgHom_apply,
      X.counit_identityComponentIdempotent, sub_self])

end FF

end ThreeAdicPlan

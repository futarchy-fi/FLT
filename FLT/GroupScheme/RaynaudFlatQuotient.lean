/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudClosureFactorization

/-!
# Integral models of prescribed generic quotients

Contract the coordinate algebra of a generic quotient inside the coordinate
algebra of the chosen integral source. This retains both the quotient model
and an integral map to it, in contrast to the existential finite-flat predicate.
The integral map is injective on coordinate rings and surjective on generic
points. Faithful flatness over the quotient coordinate ring is not asserted.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace BialgHom

variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]
    [Module.Flat R B] [Module.Flat R C]

/-- Lift an algebra factorization through an injective bialgebra map when the
two target modules are flat over the base ring. -/
def factorOfInjectiveOfFlat (k : B →ₐc[R] C) (hk : Function.Injective k)
    (i : A →ₐc[R] C) (f : A →ₐ[R] B)
    (hcomp : k.toAlgHom.comp f = i.toAlgHom) : A →ₐc[R] B := by
  apply BialgHom.ofAlgHom f
  · ext a
    calc
      Coalgebra.counit (f a) = Coalgebra.counit (k (f a)) :=
        (CoalgHomClass.counit_comp_apply k (f a)).symm
      _ = Coalgebra.counit (i a) := by
        rw [show k (f a) = i a from AlgHom.congr_fun hcomp a]
      _ = Coalgebra.counit a := CoalgHomClass.counit_comp_apply i a
  · ext a
    apply TensorProduct.map_injective_of_flat_flat k.toLinearMap k.toLinearMap hk hk
    change TensorProduct.map k.toLinearMap k.toLinearMap
      (TensorProduct.map f.toLinearMap f.toLinearMap (Coalgebra.comul a)) =
      TensorProduct.map k.toLinearMap k.toLinearMap (Coalgebra.comul (f a))
    rw [TensorProduct.map_map]
    have hlin : k.toLinearMap.comp f.toLinearMap = i.toLinearMap :=
      congrArg AlgHom.toLinearMap hcomp
    rw [hlin]
    calc
      TensorProduct.map i.toLinearMap i.toLinearMap (Coalgebra.comul a) =
          Coalgebra.comul (i a) := CoalgHomClass.map_comp_comul_apply i a
      _ = Coalgebra.comul (k (f a)) := by
        rw [show k (f a) = i a from AlgHom.congr_fun hcomp a]
      _ = TensorProduct.map k.toLinearMap k.toLinearMap (Coalgebra.comul (f a)) :=
        (CoalgHomClass.map_comp_comul_apply k (f a)).symm

end BialgHom

namespace ThreeAdicPlan

open HopfAlgebra.IntegralClosure

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    {X Y : FF R K}

/-- Integral coordinates whose generic values come from a specified quotient. -/
abbrev GenericGaloisHom.quotientCoordinates (q : GenericGaloisHom X Y) :
    Subalgebra R X.CoordinateRing :=
  contraction R K X.CoordinateRing q.toBialgHom.toAlgHom.range

/-- The contracted quotient coordinates inherit the generic Hopf operations. -/
@[instance_reducible]
instance GenericGaloisHom.quotientCoordinatesHopfAlgebra (q : GenericGaloisHom X Y) :
    HopfAlgebra R q.quotientCoordinates :=
  contractionHopfAlgebra R K X.CoordinateRing q.toBialgHom.toAlgHom.range
    (isGenericHopfSubalgebra_range R K X.CoordinateRing
      (K ⊗[R] Y.CoordinateRing) q.toBialgHom)

/-- The integral quotient coordinate ring is finite flat over the original base. -/
instance GenericGaloisHom.quotientCoordinatesFiniteFlat (q : GenericGaloisHom X Y) :
    HopfAlgebra.IsFiniteFlat R q.quotientCoordinates := by
  let : Module.Finite R q.quotientCoordinates :=
    contraction_finite R K X.CoordinateRing q.toBialgHom.toAlgHom.range
  let : Module.Flat R q.quotientCoordinates :=
    contraction_flat R K X.CoordinateRing q.toBialgHom.toAlgHom.range
  exact ⟨⟩

/-- Inclusion of the contracted quotient coordinate ring is a bialgebra map. -/
def GenericGaloisHom.quotientInclusion (q : GenericGaloisHom X Y) :
    q.quotientCoordinates →ₐc[R] X.CoordinateRing :=
  { __ := q.quotientCoordinates.val
    __ := q.quotientCoordinates.val.toLinearMap
    counit_comp := rfl
    map_comp_comul := by
      ext d
      exact contractionComul_compat R K X.CoordinateRing q.toBialgHom.toAlgHom.range
        (isGenericHopfSubalgebra_range R K X.CoordinateRing
          (K ⊗[R] Y.CoordinateRing) q.toBialgHom) d }

/-- Inclusion of quotient coordinates after extension to the generic field. -/
def GenericGaloisHom.quotientInclusionGeneric (q : GenericGaloisHom X Y) :
    K ⊗[R] q.quotientCoordinates →ₐc[K] K ⊗[R] X.CoordinateRing :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) q.quotientInclusion

/-- The generic inclusion is the inclusion of the localized contraction. -/
theorem GenericGaloisHom.quotientInclusionGeneric_apply (q : GenericGaloisHom X Y)
    (x : K ⊗[R] q.quotientCoordinates) :
    q.quotientInclusionGeneric x =
      (baseChangeEquiv R K X.CoordinateRing q.toBialgHom.toAlgHom.range x).val := by
  change q.quotientInclusionGeneric x =
    (baseChangeMap R K X.CoordinateRing q.toBialgHom.toAlgHom.range x).val
  rw [← localizedInclusion_eq_val_baseChangeMap]
  induction x using TensorProduct.inductionOn with
  | tmul k d => rfl
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

/-- The generic inclusion of the quotient coordinate ring is injective. -/
theorem GenericGaloisHom.quotientInclusionGeneric_injective (q : GenericGaloisHom X Y) :
    Function.Injective q.quotientInclusionGeneric := by
  intro a b h
  apply (baseChangeEquiv R K X.CoordinateRing q.toBialgHom.toAlgHom.range).injective
  apply Subtype.ext
  simpa only [q.quotientInclusionGeneric_apply] using h

/-- Generic identification of the contracted quotient with the prescribed quotient model. -/
def GenericGaloisHom.quotientGenericEquiv (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) :
    K ⊗[R] Y.CoordinateRing ≃ₐc[K] K ⊗[R] q.quotientCoordinates := by
  let e := baseChangeEquiv R K X.CoordinateRing q.toBialgHom.toAlgHom.range
  let a := e.symm.toAlgHom.comp q.toBialgHom.toAlgHom.rangeRestrict
  have hc : q.quotientInclusionGeneric.toAlgHom.comp a = q.toBialgHom.toAlgHom := by
    apply AlgHom.ext
    intro x
    change q.quotientInclusionGeneric (a x) = q.toBialgHom x
    rw [q.quotientInclusionGeneric_apply]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  let j := BialgHom.factorOfInjective q.quotientInclusionGeneric
    q.quotientInclusionGeneric_injective q.toBialgHom a hc
  apply BialgEquiv.ofBijective j
  constructor
  · intro x y h
    apply q.toBialgHom_injective hq
    exact (AlgHom.congr_fun hc x).symm.trans
      ((congrArg q.quotientInclusionGeneric h).trans (AlgHom.congr_fun hc y))
  · intro x
    obtain ⟨y, hy⟩ := (e x).property
    refine ⟨y, ?_⟩
    apply q.quotientInclusionGeneric_injective
    exact (AlgHom.congr_fun hc y).trans ((q.quotientInclusionGeneric_apply x).symm ▸ hy)

/-- Inclusion composed with the quotient's generic identification is the prescribed map. -/
theorem GenericGaloisHom.quotientInclusionGeneric_comp (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) :
    q.quotientInclusionGeneric.comp (q.quotientGenericEquiv hq).toBialgHom =
      q.toBialgHom := by
  ext x
  rw [BialgHom.comp_apply, q.quotientInclusionGeneric_apply]
  exact congrArg Subtype.val
    ((baseChangeEquiv R K X.CoordinateRing q.toBialgHom.toAlgHom.range).apply_symm_apply _)

/-- The finite flat model of a generic quotient obtained by contraction in the source. -/
@[implicit_reducible]
def GenericGaloisHom.flatQuotient (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) : FF R K := by
  let e := q.quotientGenericEquiv hq
  letI : Algebra.Etale K (K ⊗[R] q.quotientCoordinates) :=
    Algebra.Etale.of_equiv e.toAlgEquiv
  let a := BialgHom.precompPoints (L := AlgebraicClosure K) e.toBialgHom
  have ha : Function.Bijective a := by
    constructor
    · intro b c hbc
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      exact AlgHom.congr_fun (congrArg Additive.toMul hbc) y
    · intro b
      refine ⟨Additive.ofMul (b.toMul.comp e.symm.toAlgEquiv.toAlgHom), ?_⟩
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      exact congrArg b.toMul (e.symm_apply_apply x)
  exact { CoordinateRing := q.quotientCoordinates, Points := Y.Points
          points := Y.points.comp a, points_bijective := Y.points_bijective.comp ha }

/-- The integral map from the original model to its contracted generic quotient. -/
def GenericGaloisHom.toFlatQuotient (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) : ModelHom X (q.flatQuotient hq) :=
  q.quotientInclusion

/-- The quotient map is injective on integral coordinate rings. -/
theorem GenericGaloisHom.toFlatQuotient_injective (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) : Function.Injective (q.toFlatQuotient hq) :=
  Subtype.val_injective

/-- The integral quotient map induces the prescribed surjection on generic points. -/
@[simp] theorem GenericGaloisHom.genericHom_toFlatQuotient (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (x : X.Points) :
    genericHom (q.toFlatQuotient hq) x = q x := by
  obtain ⟨p, rfl⟩ := X.points_bijective.2 x
  rw [genericHom_points]
  change Y.points (BialgHom.precompPoints
    (q.quotientInclusionGeneric.comp (q.quotientGenericEquiv hq).toBialgHom) p) = _
  rw [q.quotientInclusionGeneric_comp]
  exact q.toBialgHom_points p

end ThreeAdicPlan

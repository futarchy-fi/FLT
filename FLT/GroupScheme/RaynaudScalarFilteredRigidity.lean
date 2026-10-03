/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarFiltration
public import FLT.GroupScheme.RaynaudScalarQuotientComparison
public import FLT.GroupScheme.RaynaudGeneralLayerDescent

/-!
# Integral rigidity by scalar-factor dévissage

Induction uses actual subgroup closures and contracted quotients. Quotient
rigidity comes from the derived rank-one theorem, and faithful flat descent
then proves rigidity of the middle map without a generic splitting.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K]

omit [IsSepClosed (ResidueField R)] [IsFractionRing R K] in
/-- A map from the trivial generic group is surjective on integral coordinates. -/
theorem ModelHom.surjective_of_generic_card_one {X Y : FF R K}
    (g : ModelHom X Y) (hX : Nat.card X.Points = 1) : Function.Surjective g := by
  let : Module.Free R X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := Module.nonempty_algEquiv_iff_finrank_eq_one.mpr
    (X.coordinate_finrank.trans hX)
  intro x
  obtain ⟨r, hr⟩ := e.surjective x
  exact ⟨algebraMap R Y.CoordinateRing r,
    (g.toAlgHom.commutes r).trans ((e.commutes r).symm.trans hr)⟩

variable (p : ℕ) [CharP (ResidueField R) p]

/-- Scalar-factor filtrations make generically invertible integral maps surjective. -/
theorem ModelHom.surjective_of_scalarFiltration
    (he : RaynaudParameters.order (p : R) < p - 1)
    {n : ℕ} {X Y : FF R K} (hX : X.HasScalarFiltration p n)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Surjective g := by
  induction n generalizing X Y with
  | zero => exact g.surjective_of_generic_card_one hX
  | succ n ih =>
    obtain ⟨S, Q, i, q, hi, hq, hex, F, hF, hfin, hp, hmod, hcomm, hdim, hS⟩ := hX
    let inv := (genericHom g).inverse hg
    let q' : GenericGaloisHom Y Q := q.comp inv
    have hq' : Function.Surjective q' := by
      intro y
      obtain ⟨x, hx⟩ := hq y
      refine ⟨genericHom g x, ?_⟩
      change q ((genericHom g).inverse hg (genericHom g x)) = y
      rw [GenericGaloisHom.inverse_apply, hx]
    let h : GenericGaloisHom Q Q := DistribMulActionHom.id _
    have hc : q'.comp (genericHom g) = h.comp q := by
      ext x
      change q ((genericHom g).inverse hg (genericHom g x)) = q x
      rw [GenericGaloisHom.inverse_apply]
    have hj : Function.Injective ((genericHom g).comp i) := hg.injective.comp hi
    apply i.middle_surjective_of_layer_maps_pid q q' hi hq hq' hex g hj h hc
    · let s : GenericGaloisHom S (i.closure hi) :=
        { toFun := id
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      apply ih (hS.of_generic_bijective s Function.bijective_id) (i.closureMap hi g hj)
      constructor
      · intro x y hxy
        simpa only [i.genericHom_closureMap hi g hj] using hxy
      · intro x
        exact ⟨x, i.genericHom_closureMap hi g hj x⟩
    · exact q.scalar_flatQuotientMap_bijective (F := F) p q' hq hq' g h (fun _ ↦ rfl)
        hc hdim he

/-- A generically bijective comparison from a scalar-filtered model is an integral isomorphism. -/
theorem ModelHom.bijective_of_scalarFiltration
    (he : RaynaudParameters.order (p : R) < p - 1)
    {n : ℕ} {X Y : FF R K} (hX : X.HasScalarFiltration p n)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Bijective g :=
  ⟨g.injective_of_generic_surjective hg.surjective,
    g.surjective_of_scalarFiltration p he hX hg⟩

end ThreeAdicPlan

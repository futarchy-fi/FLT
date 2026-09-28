/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudUnramifiedKernel
public import FLT.GroupScheme.RaynaudModelArithmetic

/-!
# Detecting scheme-theoretic kernel equations on generic points

For an unramified quotient the kernel ideal is idempotent, so geometric generic
points detect membership in it. This identifies the actual kernel equations
with the flat closure of a prescribed exact generic subgroup.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsFractionRing R K] {S X Y : FF R K}

/-- Integral coordinates of a finite flat model are separated by geometric generic points. -/
theorem FF.eq_zero_of_forall_genericPoint (X : FF R K) (a : X.CoordinateRing)
    (h : ∀ p : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K, p (1 ⊗ₜ[R] a) = 0) :
    a = 0 := by
  apply Algebra.TensorProduct.includeRight_injective (A := K) (IsFractionRing.injective R K)
  change (1 ⊗ₜ[R] a : K ⊗[R] X.CoordinateRing) = 1 ⊗ₜ[R] (0 : X.CoordinateRing)
  rw [TensorProduct.tmul_zero]
  apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing)).injective
  ext p
  exact (h p).trans (map_zero p).symm

/-- Membership in a finitely generated idempotent ideal is detected on the generic
points that annihilate the ideal. -/
theorem FF.mem_idempotentIdeal_iff (X : FF R K) (I : Ideal X.CoordinateRing)
    (hI : I.FG) (hi : IsIdempotentElem I) (a : X.CoordinateRing) :
    a ∈ I ↔ ∀ p : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K,
      (∀ b ∈ I, p (1 ⊗ₜ[R] b) = 0) → p (1 ⊗ₜ[R] a) = 0 := by
  constructor
  · exact fun ha p hp ↦ hp a ha
  · intro ha
    obtain ⟨e, he, rfl⟩ := (I.isIdempotentElem_iff_of_fg hI).mp hi
    have hz : (1 - e) * a = 0 := by
      apply X.eq_zero_of_forall_genericPoint
      intro p
      let t := Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing p
      change t ((1 - e) * a) = 0
      have ht : IsIdempotentElem (t e) := he.map t
      rcases IsIdempotentElem.iff_eq_zero_or_one.mp ht with h0 | h1
      · have hpa : t a = 0 := ha p (by
          intro b hb
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
          change t (c * e) = 0
          rw [map_mul, h0, mul_zero])
        rw [map_mul, hpa, mul_zero]
      · rw [map_mul, map_sub, map_one, h1, sub_self, zero_mul]
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨a, ?_⟩
    have h := sub_eq_zero.mp (show a - e * a = 0 by simpa only [sub_mul, one_mul] using hz)
    exact (mul_comm a e).trans h.symm

omit [PerfectField K] [IsFractionRing R K] in
/-- An integral model map sends a geometric generic point to zero exactly when
its coordinate evaluation agrees with the augmentation. -/
theorem ModelHom.genericHom_eq_zero_iff_counit (g : ModelHom X Y)
    (p : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K) :
    genericHom g (X.points (Additive.ofMul p)) = 0 ↔
      ∀ a : Y.CoordinateRing, p (1 ⊗ₜ[R] g a) =
        algebraMap R (AlgebraicClosure K) (Coalgebra.counit (R := R) a) := by
  let t := Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing p
  have hz := ModelHom.genericHom_zero X Y (X.points (Additive.ofMul p))
  constructor
  · intro h a
    have he : BialgHom.precompPoints g.baseChange (Additive.ofMul p) =
        BialgHom.precompPoints (ModelHom.zero X Y).baseChange (Additive.ofMul p) := by
      apply Y.points_bijective.1
      rw [← genericHom_points, ← genericHom_points, h, hz]
    have heval := congrArg (fun t : Additive (K ⊗[R] Y.CoordinateRing →ₐ[K] AlgebraicClosure K) ↦
      t.toMul (1 ⊗ₜ[R] a)) he
    change t (g a) = t (algebraMap R X.CoordinateRing (Coalgebra.counit (R := R) a)) at heval
    exact heval.trans (t.commutes _)
  · intro h
    have he : BialgHom.precompPoints g.baseChange (Additive.ofMul p) =
        BialgHom.precompPoints (ModelHom.zero X Y).baseChange (Additive.ofMul p) := by
      apply Additive.toMul.injective
      apply (Bialgebra.restrictPoints R K (AlgebraicClosure K) Y.CoordinateRing).injective
      apply AlgHom.ext
      intro a
      change t (g a) = t (algebraMap R X.CoordinateRing (Coalgebra.counit (R := R) a))
      exact (h a).trans (t.commutes _).symm
    rw [genericHom_points, he, ← genericHom_points, hz]

variable [IsDedekindDomain R]

/-- A generic point annihilates the actual quotient-kernel ideal exactly when its
image under the prescribed generic quotient is zero. -/
theorem GenericGaloisHom.quotientKernelIdeal_vanish_iff
    (q : GenericGaloisHom X Y) (hq : Function.Surjective q)
    (p : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K) :
    (∀ b ∈ q.quotientKernelIdeal, p (1 ⊗ₜ[R] b) = 0) ↔
      q (X.points (Additive.ofMul p)) = 0 := by
  let t := Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing p
  let g := q.toFlatQuotient hq
  have hc := g.genericHom_eq_zero_iff_counit p
  rw [q.genericHom_toFlatQuotient] at hc
  change q (X.points (Additive.ofMul p)) = 0 ↔
    ∀ d : q.quotientCoordinates, p (1 ⊗ₜ[R] q.quotientInclusion d) =
      algebraMap R (AlgebraicClosure K) (Coalgebra.counit (R := R) d) at hc
  constructor
  · intro h
    apply hc.mpr
    intro d
    let ε := Bialgebra.counitAlgHom R q.quotientCoordinates
    have hd : d - algebraMap R q.quotientCoordinates (ε d) ∈ RingHom.ker ε.toRingHom := by
      change ε (d - algebraMap R q.quotientCoordinates (ε d)) = 0
      simp only [map_sub, ε.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have he := h _ (Ideal.mem_map_of_mem q.quotientInclusion.toAlgHom.toRingHom hd)
    change (t.comp q.quotientInclusion.toAlgHom)
      (d - algebraMap R q.quotientCoordinates (ε d)) = 0 at he
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at he
    exact he
  · intro h
    have hv := hc.mp h
    have hi : q.quotientKernelIdeal ≤ RingHom.ker t.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro d hd
      change t (q.quotientInclusion d) = 0
      have hd' : Coalgebra.counit (R := R) d = 0 := hd
      exact (hv d).trans (by rw [hd', map_zero])
    exact fun b hb ↦ hi hb

omit [IsFractionRing R K] [IsDedekindDomain R] in
/-- The ideal of the flat closure consists exactly of the integral functions that
vanish on the image of the generic subgroup. -/
theorem GenericGaloisHom.mem_closureIdeal_iff_vanish
    (i : GenericGaloisHom S X) (a : X.CoordinateRing) :
    a ∈ i.closureIdeal ↔
      ∀ p : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K,
        (∃ s, i s = X.points (Additive.ofMul p)) → p (1 ⊗ₜ[R] a) = 0 := by
  constructor
  · intro ha p hp
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, rfl⟩ := S.points_bijective.2 s
    have he : BialgHom.precompPoints i.toBialgHom t = Additive.ofMul p :=
      X.points_bijective.1 ((i.toBialgHom_points t).trans hs)
    have heval := congrArg (fun t : Additive (K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K) ↦
      t.toMul (1 ⊗ₜ[R] a)) he
    change i.toBialgHom (1 ⊗ₜ[R] a) = 0 at ha
    exact heval.symm.trans (by change t.toMul (i.toBialgHom _) = 0; rw [ha, map_zero])
  · intro ha
    change i.toBialgHom (1 ⊗ₜ[R] a) = 0
    apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
      (K ⊗[R] S.CoordinateRing)).injective
    ext t
    change t (i.toBialgHom (1 ⊗ₜ[R] a)) = t 0
    rw [map_zero]
    exact ha (t.comp i.toBialgHom.toAlgHom)
      ⟨S.points (Additive.ofMul t), (i.toBialgHom_points (Additive.ofMul t)).symm⟩

/-- For an unramified contracted quotient, the actual scheme-theoretic kernel
is exactly the flat closure of any prescribed exact generic subgroup. -/
theorem GenericGaloisHom.quotientKernelIdeal_eq_closureIdeal_of_formallyUnramified
    (i : GenericGaloisHom S X) (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    [Algebra.FormallyUnramified R q.quotientCoordinates] :
    q.quotientKernelIdeal = i.closureIdeal := by
  let : IsNoetherianRing X.CoordinateRing := IsNoetherianRing.of_finite R X.CoordinateRing
  ext a
  rw [X.mem_idempotentIdeal_iff q.quotientKernelIdeal (IsNoetherian.noetherian _)
    q.quotientKernelIdeal_isIdempotentElem, i.mem_closureIdeal_iff_vanish]
  simp only [q.quotientKernelIdeal_vanish_iff hq, hexact]

/-- Exact generic subgroup data identify the scheme kernel for an unramified
order-three quotient over the three-adic integers, without a splitting assumption. -/
theorem GenericGaloisHom.quotientKernelIdeal_eq_closureIdeal_of_unramified_order_three
    {S X Y : FF ℤ_[3] ℚ_[3]} (i : GenericGaloisHom S X) (q : GenericGaloisHom X Y)
    (hq : Function.Surjective q) (hexact : ∀ x, q x = 0 ↔ ∃ s, i s = x)
    (hY : Nat.card Y.Points = 3) [Algebra.FormallyUnramified ℤ_[3] Y.CoordinateRing] :
    q.quotientKernelIdeal = i.closureIdeal := by
  let := q.quotientCoordinates_formallyUnramified_of_order_three hq hY
  exact i.quotientKernelIdeal_eq_closureIdeal_of_formallyUnramified q hq hexact

end ThreeAdicPlan

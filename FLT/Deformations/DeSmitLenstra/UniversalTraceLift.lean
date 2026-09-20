/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.DeSmitLenstra.UniversalMoritaData
public import FLT.Deformations.DeSmitLenstra

/-!
# The universal trace lift

The representation reconstructed from the universal trace ring is a universal lift.  Existence
comes from the universal framed deformation ring and the strict Morita conjugator.  Uniqueness
follows because traces determine a morphism on the dense trace algebra and morphisms of
pro-Artinian rings are continuous.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Deformation.MoritaReconstruction

noncomputable section

open Representation

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable (n : Type) [Fintype n] [DecidableEq n]
variable [Finite (ResidueField O)]
variable (rho : G →ₜ* GL n (@ProartinianCat.residueField O _ _))

set_option maxHeartbeats 4000000 in
-- This assembles the framed universal property, Morita reconstruction, and density argument.
set_option synthInstance.maxHeartbeats 100000 in
/-- The representation reconstructed over the closed universal trace ring is a universal lift. -/
theorem exists_universalTraceLift
    [(residualLinearRepresentation O G n rho).IsAbsolutelyIrreducible.{u}] :
    ∃ sigma : (repnFunctor n G O).obj (universalTraceRingObject O G n rho),
      IsUniversalLift n G O
        (show (repnFunctor n G O).obj .residueField from rho) sigma := by
  obtain ⟨e, _he, b, _hMorita, v, c, hc, hstrict⟩ :=
    exists_universalMoritaData O G n rho
  let sigma : (repnFunctor n G O).obj (universalTraceRingObject O G n rho) :=
    ⟨universalTraceDescendedGL O G n rho e b,
      universalTraceDescendedGL_continuous O G n rho e v b c hc⟩
  obtain ⟨P, hP_res, hP_conj⟩ :=
    exists_strict_universalTraceDescendedGL_conjugator
      O G n rho e v b c hc hstrict
  refine ⟨sigma, ?_, ?_⟩
  · rw [mem_liftFunctor_iff n G O
      (show (repnFunctor n G O).obj .residueField from rho)]
    apply ContinuousMonoidHom.ext
    intro g
    change Matrix.GeneralLinearGroup.map
      (ProartinianCat.toResidueField
        (universalTraceRingObject O G n rho)).hom.toRingHom
          (universalTraceDescendedGL O G n rho e b g) = rho g
    have h := congrArg
      (Matrix.GeneralLinearGroup.map (framedResidueRingHom O G n rho))
      (hP_conj g)
    rw [map_mul, map_mul, map_inv, hP_res, one_mul, inv_one, mul_one] at h
    rw [← Matrix.GeneralLinearGroup.map_comp_apply] at h
    have hres : universalTraceRingInclusion O G n rho ≫
        ProartinianCat.toResidueField (profiniteFramedLimitObject O G n rho) =
          ProartinianCat.toResidueField (universalTraceRingObject O G n rho) :=
      Subsingleton.elim _ _
    have hring := congrArg (fun f : universalTraceRingObject O G n rho ⟶
        @ProartinianCat.residueField O _ _ ↦ f.hom.toRingHom) hres
    change (framedResidueRingHom O G n rho).comp
      (algebraMap (UniversalTraceRing O G n rho)
        (ProfiniteFramedLimit O G n rho)) =
      (ProartinianCat.toResidueField
        (universalTraceRingObject O G n rho)).hom.toRingHom at hring
    rw [← Matrix.GeneralLinearGroup.map_comp] at h
    rw [hring] at h
    have hframed := congrArg (fun r : G →* GL n (ResidueField O) ↦ r g)
      (profiniteUniversalContinuousLift_isFramedLift O G n rho)
    exact h.trans hframed
  · intro S tau htau
    let tauF : ContinuousFramedLifts O G n rho S := ⟨tau, by
      unfold IsContinuousFramedLift
      exact congrArg ContinuousMonoidHom.toMonoidHom
        ((mem_liftFunctor_iff n G O
          (show (repnFunctor n G O).obj .residueField from rho) tau).mp htau)⟩
    let F : profiniteFramedLimitObject O G n rho ⟶ S :=
      profiniteFramedLimitLiftToHom O G n rho S tauF
    let FF : ProfiniteFramedLimit O G n rho →+* S := F.hom.toRingHom
    let f : universalTraceRingObject O G n rho ⟶ S :=
      universalTraceRingInclusion O G n rho ≫ F
    let Q : GL n S := Matrix.GeneralLinearGroup.map FF P
    have hF (g : G) : Matrix.GeneralLinearGroup.map FF
        (profiniteUniversalLift O G n rho g) =
          DFunLike.coe (F := G →ₜ* GL n S) tau g := by
      have h := congrArg (fun t : ContinuousFramedLifts O G n rho S ↦ t.1 g)
        (profiniteFramedLimitHomToLift_liftToHom O G n rho S tauF)
      exact h
    have hQ_res : Matrix.GeneralLinearGroup.map
        (ProartinianCat.toResidueField S).hom.toRingHom Q = 1 := by
      have hres : F ≫ ProartinianCat.toResidueField S =
          ProartinianCat.toResidueField (profiniteFramedLimitObject O G n rho) :=
        Subsingleton.elim _ _
      have hring := congrArg (fun h : profiniteFramedLimitObject O G n rho ⟶
          @ProartinianCat.residueField O _ _ ↦ h.hom.toRingHom) hres
      change (ProartinianCat.toResidueField S).hom.toRingHom.comp FF =
        framedResidueRingHom O G n rho at hring
      calc
        _ = Matrix.GeneralLinearGroup.map (framedResidueRingHom O G n rho) P := by
          apply Units.ext
          ext i j
          exact DFunLike.congr_fun hring (P i j)
        _ = 1 := hP_res
    have hspecial (g : G) : Q *
        Matrix.GeneralLinearGroup.map f.hom.toRingHom
          (universalTraceDescendedGL O G n rho e b g) * Q⁻¹ =
            DFunLike.coe (F := G →ₜ* GL n S) tau g := by
      have h := congrArg (Matrix.GeneralLinearGroup.map FF) (hP_conj g)
      rw [map_mul, map_mul, map_inv] at h
      change Q * Matrix.GeneralLinearGroup.map f.hom.toRingHom
          (universalTraceDescendedGL O G n rho e b g) * Q⁻¹ = _ at h
      exact h.trans (hF g)
    have hf : (toRepnQuot n G O).app S ((repnFunctor n G O).map f sigma) =
        (toRepnQuot n G O).app S tau := by
      apply (repnQuot_mk_eq_iff n G O _ _).mpr
      refine ⟨Q⁻¹, ?_, fun g ↦ ?_⟩
      · rw [map_inv, hQ_res, inv_one]
      change Matrix.GeneralLinearGroup.map f.hom.toRingHom
          (universalTraceDescendedGL O G n rho e b g) = Q⁻¹ *
            DFunLike.coe (F := G →ₜ* GL n S) tau g * (Q⁻¹)⁻¹
      rw [inv_inv]
      calc
        _ = Q⁻¹ * (Q * Matrix.GeneralLinearGroup.map f.hom.toRingHom
            (universalTraceDescendedGL O G n rho e b g) * Q⁻¹) * Q := by group
        _ = _ := by rw [hspecial]
    refine ⟨f, hf, ?_⟩
    intro f' hf'
    have htrace (f'' : universalTraceRingObject O G n rho ⟶ S)
        (hf'' : (toRepnQuot n G O).app S
            ((repnFunctor n G O).map f'' sigma) =
              (toRepnQuot n G O).app S tau) (g : G) :
        f''.hom ⟨(profiniteUniversalMatrix O G n rho g).trace,
          universalTrace_mem O G n rho g⟩ =
            Matrix.trace (↑(DFunLike.coe (F := G →ₜ* GL n S) tau g) :
              Matrix n n S) := by
      obtain ⟨gamma, _hgamma_res, hgamma⟩ :=
        (repnQuot_mk_eq_iff n G O _ _).mp hf''
      have ht := congrArg (fun z : GL n S ↦ Matrix.trace (↑z : Matrix n n S))
        (hgamma g)
      change Matrix.trace
          (↑(DFunLike.coe (F := G →ₜ* GL n S)
            ((repnFunctor n G O).map f'' sigma) g) : Matrix n n S) =
        Matrix.trace ((↑gamma : Matrix n n S) *
          (↑(DFunLike.coe (F := G →ₜ* GL n S) tau g) : Matrix n n S) *
          (↑(gamma⁻¹) : Matrix n n S)) at ht
      rw [Matrix.trace_units_conj] at ht
      rw [← universalTraceDescendedGL_trace O G n rho e v b c hc g]
      exact (AddMonoidHom.map_trace f''.hom.toRingHom.toAddMonoidHom
        (↑(universalTraceDescendedGL O G n rho e b g) :
          Matrix n n (UniversalTraceRing O G n rho))).trans ht
    have hgen (g : G) :
        f'.hom ⟨(profiniteUniversalMatrix O G n rho g).trace,
          universalTrace_mem O G n rho g⟩ =
        f.hom ⟨(profiniteUniversalMatrix O G n rho g).trace,
          universalTrace_mem O G n rho g⟩ :=
      (htrace f' hf' g).trans (htrace f hf g).symm
    let A : Subalgebra O (ProfiniteFramedLimit O G n rho) :=
      Algebra.adjoin O (Set.range fun g : G ↦
        (profiniteUniversalMatrix O G n rho g).trace)
    let inc : A →ₐ[O] UniversalTraceRing O G n rho :=
      Subalgebra.inclusion (Subalgebra.le_topologicalClosure A)
    have hA : f'.hom.toAlgHom.comp inc = f.hom.toAlgHom.comp inc := by
      apply AlgHom.adjoin_ext
      intro x hx
      rcases hx with ⟨g, rfl⟩
      exact hgen g
    have hdense : DenseRange
        (Set.inclusion (Subalgebra.le_topologicalClosure A)) := by
      rw [denseRange_inclusion_iff (Subalgebra.le_topologicalClosure A)]
      rw [Subalgebra.topologicalClosure_coe]
    apply ProartinianCat.hom_ext
    apply DFunLike.ext _ _
    intro x
    apply congr_fun (hdense.equalizer f'.hom.cont f.hom.cont ?_) x
    funext a
    change f'.hom (inc a) = f.hom (inc a)
    exact DFunLike.congr_fun hA a

end

end Deformation.MoritaReconstruction

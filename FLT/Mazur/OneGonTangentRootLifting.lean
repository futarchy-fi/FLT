/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonTangentEtaleCover

/-!
# Unique infinitesimal lifting of a chosen nodal tangent

The actual tangent algebra is etale. Consequently a tangent chosen on an
arbitrary nilpotent reduction lifts uniquely, even in mixed characteristic.
This retains the specified root instead of making a new splitting choice.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial W)

/-- A root of the actual tangent equation defines its universal coefficient map. -/
def tangentRootHom (s : A)
    (hs : s ^ 2 + algebraMap R A W.a₁ * s = algebraMap R A W.a₂) : S →ₐ[R] A :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R A) s
    (by
      change (nodeTangentPolynomial W).eval₂ (algebraMap R A) s = 0
      rw [nodeTangentPolynomial_eval₂, sub_eq_zero]
      exact hs)

/-- The universal root map takes the original distinguished root to the specified one. -/
@[simp] theorem tangentRootHom_root (s : A)
    (hs : s ^ 2 + algebraMap R A W.a₁ * s = algebraMap R A W.a₂) :
    tangentRootHom W s hs r = s := AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Every coefficient map out of the tangent algebra evaluates to an actual tangent root. -/
theorem tangentHom_root_equation (g : S →ₐ[R] A) :
    g r ^ 2 + algebraMap R A W.a₁ * g r = algebraMap R A W.a₂ := by
  have h := congrArg g (nodeTangentRoot_equation W)
  simpa only [map_sub, map_add, map_pow, map_mul, map_zero, AlgHom.commutes,
    sub_eq_zero] using h

/-- Two actual tangent roots agreeing on a nilpotent reduction agree before reduction. -/
theorem tangentRoot_unique (hb : IsUnit W.b₂) (I : Ideal A) (hI : IsNilpotent I)
    (s t : A)
    (hs : s ^ 2 + algebraMap R A W.a₁ * s = algebraMap R A W.a₂)
    (ht : t ^ 2 + algebraMap R A W.a₁ * t = algebraMap R A W.a₂)
    (hst : Ideal.Quotient.mk I s = Ideal.Quotient.mk I t) : s = t := by
  let _ := tangentAlgebra_etale W hb
  have h : tangentRootHom W s hs = tangentRootHom W t ht := by
    apply Algebra.FormallyUnramified.lift_unique I hI
    apply AdjoinRoot.algHom_ext
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, tangentRootHom_root] using hst
  simpa only [tangentRootHom_root] using AlgHom.congr_fun h r

/-- A specified residual tangent lifts uniquely through an arbitrary nilpotent thickening. -/
theorem existsUnique_tangentRoot_lift (hb : IsUnit W.b₂) (I : Ideal A)
    (hI : IsNilpotent I) (s₀ : A ⧸ I)
    (hs₀ : s₀ ^ 2 + algebraMap R (A ⧸ I) W.a₁ * s₀ = algebraMap R (A ⧸ I) W.a₂) :
    ∃! s : A, s ^ 2 + algebraMap R A W.a₁ * s = algebraMap R A W.a₂ ∧
      Ideal.Quotient.mk I s = s₀ := by
  let _ := tangentAlgebra_etale W hb
  let g₀ := tangentRootHom W s₀ hs₀
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift I hI g₀
  have hr : Ideal.Quotient.mk I (g r) = s₀ := by
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, g₀, tangentRootHom_root]
      using AlgHom.congr_fun hg r
  refine ⟨g r, ⟨tangentHom_root_equation W g, hr⟩, ?_⟩
  intro t ht
  exact tangentRoot_unique W hb I hI t (g r) ht.1
    (tangentHom_root_equation W g) (ht.2.trans hr.symm)

end FLT.Mazur.OneGonInfinitesimal

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AlgebraicPointFiniteDescent
public import FLT.Mazur.OriginalFiniteCoefficientOrbit

/-!
# Algebraic point descent above the unchanged original base

The finite field factorization is performed in the residue fiber and then
returned to the original over category. It retains the whole original
parameter morphism and the precise coefficient-restriction map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalAlgebraicPointDescent
open OriginalFiniteCoefficientOrbit
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  {S : Scheme} (t : Spec (.of k) ⟶ S) {V : Over S} [LocallyOfFiniteType V.hom]

/-- Every algebraic parameter point descends finitely without replacing its original base. -/
theorem exists_finite_original_factor (p : coefficientTest (K := K) t ⟶ V) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
      (i : L →ₐ[k] K) (q : coefficientTest (K := L) t ⟶ V),
      restriction t i ≫ q = p := by
  let Y := pullback V.hom t
  let c := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p' : Spec (.of K) ⟶ Y := pullback.lift p.left c p.w
  obtain ⟨L, hL, hA, hfin, i, q, hq, hp⟩ :=
    AlgebraicPointFiniteDescent.exists_finite_factor (pullback.snd V.hom t)
      p' (pullback.lift_snd _ _ _)
  let _ := hL
  let _ := hA
  let _ := hfin
  let q' : coefficientTest (K := L) t ⟶ V := Over.homMk
    (q ≫ pullback.fst V.hom t) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hq]
      rfl)
  refine ⟨L, hL, hA, hfin, i, q', ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom i.toRingHom) ≫ (q ≫ pullback.fst V.hom t) = p.left
  rw [← Category.assoc, hp]
  exact pullback.lift_fst _ _ _

end FLT.Mazur.OriginalAlgebraicPointDescent

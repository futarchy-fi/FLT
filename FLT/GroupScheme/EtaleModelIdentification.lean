/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FiniteFlatIso
public import FLT.GroupScheme.RaynaudEtaleExtension

/-!
# Identifying integral étale models from their geometric points

Over a Dedekind domain, every generic morphism from an integral étale model
extends uniquely. Thus an equivariant additive equivalence between the points of
two integral étale models gives a compatible integral bialgebra equivalence.
The étaleness hypotheses refer to the actual integral models; unramified generic
points alone do not supply them.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]

/-- Integral generic coordinates suffice to extend a point morphism over a Dedekind domain. -/
theorem extend_generic_morphism_of_integral_coordinates
    (X Y : FF R K) (f : GenericGaloisHom X Y)
    (hf : ∀ y : Y.CoordinateRing, ∃ x : X.CoordinateRing,
      f.toBialgHom (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] x) :
    ∃! fO : ModelHom X Y, genericHom fO = f := by
  let e := BialgEquiv.ofBijective f.graphFst
    ⟨f.graphFst_injective, f.graphFst_surjective_of_integral hf⟩
  let g : ModelHom X f.graphClosure := e.symm.toBialgHom
  have hg : ∀ x : X.Points, genericHom g x = x := by
    have he : g.comp f.graphFst = BialgHom.id R X.CoordinateRing := by
      ext a
      exact e.symm_apply_apply a
    intro x
    have h := congrArg (fun a : ModelHom X X ↦ genericHom a x) he
    rw [genericHom_comp] at h
    simpa using h
  let fO : ModelHom X Y := g.comp f.graphSnd
  have hO : genericHom fO = f := by
    ext x
    change genericHom (g.comp f.graphSnd) x = f x
    rw [genericHom_comp, f.genericHom_graphSnd, hg]
  exact ⟨fO, hO, fun gO hgO ↦ genericHom_injective X Y (hgO.trans hO.symm)⟩

/-- An integral étale source contains all integral values of generic coordinate maps. -/
theorem GenericGaloisHom.integral_coordinates_of_etale
    {X Y : FF R K} [Algebra.Etale R X.CoordinateRing]
    (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] x := by
  let g : Y.CoordinateRing →ₐ[R] K ⊗[R] X.CoordinateRing :=
    (f.toBialgHom.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hy : IsIntegral R (g y) := (Algebra.IsIntegral.isIntegral y).map g
  obtain ⟨x, hx⟩ := Algebra.TensorProduct.exists_includeRight_eq_of_isIntegral (g y) hy
  exact ⟨x, hx.symm⟩

/-- Every generic morphism from an integral étale source extends uniquely. -/
theorem extend_generic_morphism_of_etale (X Y : FF R K)
    [Algebra.Etale R X.CoordinateRing] (f : GenericGaloisHom X Y) :
    ∃! fO : ModelHom X Y, genericHom fO = f :=
  extend_generic_morphism_of_integral_coordinates X Y f f.integral_coordinates_of_etale

/-- Integral étale models are identified by any specified equivariant point equivalence. -/
theorem exists_iso_of_etale (X Y : FF R K)
    [Algebra.Etale R X.CoordinateRing] [Algebra.Etale R Y.CoordinateRing]
    (e : X.Points ≃+ Y.Points) (he : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x,
      e (σ • x) = σ • e x) :
    ∃ i : X.Iso Y, ∀ x, genericHom i.toBialgHom x = e x := by
  let f : GenericGaloisHom X Y := { toAddMonoidHom := e.toAddMonoidHom, map_smul' := he }
  let g : GenericGaloisHom Y X :=
    { toAddMonoidHom := e.symm.toAddMonoidHom
      map_smul' := fun σ y ↦ by
        apply e.injective
        change e (e.symm (σ • y)) = e (σ • e.symm y)
        rw [e.apply_symm_apply, he, e.apply_symm_apply] }
  obtain ⟨fO, hfO, _⟩ := extend_generic_morphism_of_etale X Y f
  obtain ⟨gO, hgO, _⟩ := extend_generic_morphism_of_etale Y X g
  have hgf : ∀ x, genericHom gO (genericHom fO x) = x := by
    intro x
    rw [hfO, hgO]
    exact e.symm_apply_apply x
  have hfg : ∀ y, genericHom fO (genericHom gO y) = y := by
    intro y
    rw [hfO, hgO]
    exact e.apply_symm_apply y
  exact ⟨FF.isoOfGenericInverse fO gO hgf hfg, fun x ↦ DFunLike.congr_fun hfO x⟩

/-- The preceding integral comparison in the bundled rational-point interface. -/
theorem FiniteFlatObject.exists_iso_of_etale
    {S : Type} [CommRing S] [Algebra S ℚ] [IsDedekindDomain S] [IsFractionRing S ℚ]
    (H J : FiniteFlatObject S)
    [Algebra.Etale S H.model.CoordinateRing] [Algebra.Etale S J.model.CoordinateRing]
    (e : H.points ≃+ J.points)
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x,
      e (σ • x) = σ • e x) :
    ∃ i : H.Iso J, ∀ x, FiniteFlatObject.pointMap i.toBialgHom x = e x := by
  let : Algebra.Etale S H.toFF.CoordinateRing :=
    inferInstanceAs (Algebra.Etale S H.model.CoordinateRing)
  let : Algebra.Etale S J.toFF.CoordinateRing :=
    inferInstanceAs (Algebra.Etale S J.model.CoordinateRing)
  exact ThreeAdicPlan.exists_iso_of_etale H.toFF J.toFF e he

end ThreeAdicPlan

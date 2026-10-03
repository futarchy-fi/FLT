/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarFilteredRigidity

/-!
# Prescribed extension for scalar-filtered models

Transport the generic filtration to the actual graph closure. Its first
projection is an integral isomorphism, so the second projection supplies
the prescribed extension and the integral pullback of every coordinate.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing
open scoped TensorProduct

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K]
  (p : ℕ) [CharP (ResidueField R) p]
  (he : RaynaudParameters.order (p : R) < p - 1)
  {n : ℕ} {X Y : FF R K} (hX : X.HasScalarFiltration p n) (f : GenericGaloisHom X Y)

include he hX

/-- Every prescribed generic map from a scalar-filtered model extends uniquely. -/
theorem extend_from_scalar_filtered_model : ∃! g : ModelHom X Y, genericHom g = f := by
  let s : GenericGaloisHom X f.graphClosure :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hG := hX.of_generic_bijective s Function.bijective_id
  have hf : Function.Bijective (genericHom f.graphFst) := by
    constructor
    · intro x y hxy
      simpa only [f.genericHom_graphFst] using hxy
    · exact fun x ↦ ⟨x, f.genericHom_graphFst x⟩
  let e := BialgEquiv.ofBijective f.graphFst
    (f.graphFst.bijective_of_scalarFiltration p he hG hf)
  let a : ModelHom X f.graphClosure := e.symm.toBialgHom
  have ha : ∀ x : X.Points, genericHom a x = x := by
    have hid : a.comp f.graphFst = BialgHom.id R X.CoordinateRing := by
      ext x
      exact e.symm_apply_apply x
    intro x
    have h := congrArg (fun g : ModelHom X X ↦ genericHom g x) hid
    simpa only [genericHom_comp, f.genericHom_graphFst, genericHom_id] using h
  have hg : genericHom (a.comp f.graphSnd) = f := by
    ext x
    rw [genericHom_comp, f.genericHom_graphSnd, ha]
  exact ⟨a.comp f.graphSnd, hg, fun g hg' ↦ genericHom_injective X Y (hg'.trans hg.symm)⟩

/-- Each coordinate of the prescribed pullback is integral in the original source model. -/
theorem GenericGaloisHom.integral_of_scalarFiltration (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[R] y) = 1 ⊗ₜ[R] x := by
  obtain ⟨g, hg, _⟩ := extend_from_scalar_filtered_model p he hX f
  refine ⟨g y, ?_⟩
  rw [← hg, ModelHom.toBialgHom_genericHom]
  rfl

end ThreeAdicPlan

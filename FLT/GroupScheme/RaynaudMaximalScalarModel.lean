/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtremalActions
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Maximal scalar models from an actual finite-flat Galois module

Unpack the finite-flat witness, construct its maximal model, and transport
the coefficient module through the derived generic identification.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K F W : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
  [Field F] [AddCommGroup W] [Module F W]
  [DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W]
  [SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) W]

/-- A finite-flat rank-one scalar module has a maximal model with derived scalar lifts. -/
theorem exists_maximal_scalar_model
    (hW : GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) W)
    (hdim : Module.finrank F W = 1) :
    ∃ (M : FF R K) (_ : Module F M.Points)
      (f : W ≃ₗ[F] M.Points) (lift : F → ModelHom M M),
      (∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) w, f (σ • w) = σ • f w) ∧
      Module.finrank F M.Points = 1 ∧
      (∀ a x, genericHom (lift a) x = a • x) ∧
      lift 0 = ModelHom.zero M M ∧ lift 1 = BialgHom.id R M.CoordinateRing ∧
      (∀ a b, lift (a + b) = (lift a).add (lift b)) ∧
      (∀ a b, lift (a * b) = (lift b).comp (lift a)) ∧
      (∀ (Y : FF R K) (g : GenericGaloisHom M Y), ∃! h : ModelHom M Y, genericHom h = g) := by
  rcases hW with ⟨H, _, _, _, _, j, hj⟩
  let X : FF R K := { CoordinateRing := H, Points := W, points := j, points_bijective := hj }
  obtain ⟨M, f, lift, hf, hmax, hlift, h0, h1, hadd, hmul⟩ :=
    exists_maximal_model_scalar_action (F := F) X
  let e : M.Points ≃+ W := (AddEquiv.ofBijective f.toAddMonoidHom hf).symm
  let : Module F M.Points := e.module F
  let l : W ≃ₗ[F] M.Points := (e.linearEquiv F).symm
  refine ⟨M, inferInstance, l, lift, ?_, ?_, ?_, h0, h1, hadd, hmul, hmax⟩
  · exact fun σ w ↦ f.map_smul σ w
  · exact (e.linearEquiv F).finrank_eq.trans hdim
  · intro a y
    obtain ⟨x, rfl⟩ := hf.2 y
    exact (hlift a x).trans (l.map_smul a x)

end ThreeAdicPlan

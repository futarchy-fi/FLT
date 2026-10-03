/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtremalScalarIso

/-!
# Prescribed extension from rank-one scalar models

The maximum-to-minimum isomorphism factors through the original model.
This identifies the original model with its maximum, even when integral
scalar lifts on the original model have not been supplied or constructed.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Finite F]
  (X : FF R K) [Module F X.Points]
  [SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)

include hdim in
/-- Every prescribed generic map out of a rank-one scalar model extends uniquely. -/
theorem extend_from_rank_one_scalar_model (he : RaynaudParameters.order (p : R) < p - 1)
    (Y : FF R K) (g : GenericGaloisHom X Y) : ∃! h : ModelHom X Y, genericHom h = g := by
  obtain ⟨M, N, fm, fn, e, hfm, _, hid, hmax, hmin⟩ :=
    exists_extremal_scalar_iso X p hdim he
  obtain ⟨a, ha, _⟩ := hmax X (fm.inverse hfm)
  obtain ⟨b, hb, _⟩ := hmin X fn
  have hab : a.comp b = e.toBialgHom := by
    apply genericHom_injective M N
    ext m
    obtain ⟨x, rfl⟩ := hfm.surjective m
    rw [genericHom_comp, ha, hb, GenericGaloisHom.inverse_apply]
    exact (DFunLike.congr_fun hid x).symm
  have ha_surj : Function.Surjective a := by
    intro m
    obtain ⟨n, hn⟩ := e.surjective m
    exact ⟨b n, (DFunLike.congr_fun hab n).trans hn⟩
  have ha_inj : Function.Injective a := a.injective_of_generic_surjective (by
    rw [ha]
    exact (AddEquiv.ofBijective fm.toAddMonoidHom hfm).symm.surjective)
  let ea : M.Iso X := BialgEquiv.ofBijective a ⟨ha_inj, ha_surj⟩
  have hinv : ea.symm.toBialgHom.comp a = BialgHom.id R X.CoordinateRing := by
    ext x
    exact ea.symm_apply_apply x
  obtain ⟨k, hk, _⟩ := hmax Y (g.comp (genericHom a))
  have hext : genericHom (ea.symm.toBialgHom.comp k) = g := by
    ext x
    rw [genericHom_comp, hk]
    change g (genericHom a (genericHom ea.symm.toBialgHom x)) = g x
    rw [← genericHom_comp, hinv, genericHom_id]
  exact ⟨ea.symm.toBialgHom.comp k, hext,
    fun h hh ↦ genericHom_injective X Y (hh.trans hext.symm)⟩

end ThreeAdicPlan

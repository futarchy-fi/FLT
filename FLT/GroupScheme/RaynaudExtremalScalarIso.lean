/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudIdentifiedScalarIso
public import FLT.GroupScheme.RaynaudExtremalActions

/-!
# The independently constructed scalar extrema are isomorphic

Construct both extremal models and their scalar actions first. Their
prescribed generic identification extends from the maximum, and the proved
coordinate-scaling theorem makes that actual integral map an isomorphism.
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
/-- Construct the maximum and minimum and prove their prescribed comparison is an isomorphism. -/
theorem exists_extremal_scalar_iso (he : RaynaudParameters.order (p : R) < p - 1) :
    ∃ (M N : FF R K) (fm : GenericGaloisHom X M) (fn : GenericGaloisHom X N) (e : M.Iso N),
      Function.Bijective fm ∧ Function.Bijective fn ∧
      (genericHom e.toBialgHom).comp fm = fn ∧
      (∀ (Y : FF R K) (g : GenericGaloisHom M Y), ∃! h : ModelHom M Y, genericHom h = g) ∧
      (∀ (Y : FF R K) (g : GenericGaloisHom Y N), ∃! h : ModelHom Y N, genericHom h = g) := by
  classical
  let : Fintype F := Fintype.ofFinite _
  obtain ⟨_, hunit, _⟩ := henselian_group_characters (R := R) Fˣ (by
    rw [scalar_units_card_residue (F := F) p]; exact neg_ne_zero.mpr one_ne_zero)
  let : Invertible (Fintype.card Fˣ : R) := hunit.invertible
  obtain ⟨M, fm, sx, hfm, hmax, hsx, hx0, hx1, hxa, hxm⟩ :=
    exists_maximal_model_scalar_action (F := F) X
  obtain ⟨N, fn, sy, hfn, hmin, hsy, hy0, hy1, hya, hym⟩ :=
    exists_minimal_model_scalar_action (F := F) X
  let g := fn.comp (fm.inverse hfm)
  have hg : Function.Bijective g := hfn.comp
    (AddEquiv.ofBijective fm.toAddMonoidHom hfm).symm.bijective
  obtain ⟨f, hf, _⟩ := hmax N g
  have hid : (genericHom f).comp fm = fn := by
    ext x
    change genericHom f (fm x) = fn x
    rw [hf]
    change fn (fm.inverse hfm (fm x)) = fn x
    rw [GenericGaloisHom.inverse_apply]
  have hbij := f.bijective_of_identified_rank_one_scalars fm fn hfm hfn
    (by simpa only [hf] using hg) hid sx sy hx0 hy0 hx1 hy1 hxm hym hxa hya hsx hsy p hdim he
  exact ⟨M, N, fm, fn, BialgEquiv.ofBijective f hbij, hfm, hfn, hid, hmax, hmin⟩

end ThreeAdicPlan

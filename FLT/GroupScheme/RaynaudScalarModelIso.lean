/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudFundamentalScalingUnits

/-!
# Rigidity of actual rank-one scalar models

A generically bijective scalar-compatible integral map has unit coordinate
scalings below the ramification bound. The derived finite generation theorem
then proves it is an isomorphism on the integral coordinate algebras.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] {X Y : FF R K}
  [Module F X.Points] [Module F Y.Points] (f : ModelHom X Y)
  (sx : F → ModelHom X X) (sy : F → ModelHom Y Y)
  (hx0 : sx 0 = ModelHom.zero X X) (hy0 : sy 0 = ModelHom.zero Y Y)
  (hx1 : sx 1 = BialgHom.id R X.CoordinateRing)
  (hy1 : sy 1 = BialgHom.id R Y.CoordinateRing)
  (hxm : ∀ a b, sx (a * b) = (sx b).comp (sx a))
  (hym : ∀ a b, sy (a * b) = (sy b).comp (sy a))
  (hxa : ∀ a b, sx (a + b) = (sx a).add (sx b))
  (hya : ∀ a b, sy (a + b) = (sy a).add (sy b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdx : Module.finrank F X.Points = 1) (hdy : Module.finrank F Y.Points = 1)
  (hsx : ∀ a x, genericHom (sx a) x = a • x)
  (hsy : ∀ a y, genericHom (sy a) y = a • y)

include hx0 hy0 hx1 hy1 hxm hym hxa hya hdx hdy hsx hsy in
/-- Every scalar-compatible generic isomorphism already integral is an integral isomorphism. -/
theorem ModelHom.bijective_of_rank_one_scalars
    (hf : Function.Bijective (genericHom f))
    (hlinear : ∀ (a : F) x, genericHom f (a • x) = a • genericHom f x)
    (he : RaynaudParameters.order (p : R) < p - 1) : Function.Bijective f := by
  let hc := f.scalar_compatible sx sy hsx hsy hlinear
  obtain ⟨r, _, hr⟩ := FiniteField.card F p
  obtain ⟨e⟩ := exists_scalar_residue_embedding (R := R) (F := F) p
  refine ⟨f.injective_of_generic_surjective hf.surjective, ?_⟩
  apply (AlgHom.range_eq_top f.toAlgHom).mp
  apply top_unique
  rw [← X.finite_fundamental_adjoin_eq_top sx hx0 hx1 hxm hxa p hdx hsx e r hr]
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  obtain ⟨u, hu⟩ := f.isUnit_fundamental_scaling sx sy hx0 hy0 hx1 hy1 hxm hym hxa hya hc
    p hdx hdy hsx hsy e r hr hf.surjective he i
  refine ⟨(↑u⁻¹ : R) • Y.fundamentalCoordinate p sy hy1 hym hdy hsy e i, ?_⟩
  change f ((↑u⁻¹ : R) •
    Y.characterGenerator sy hy1 hym p hdy hsy (fundamentalCharacter p e ^ (p ^ i.val))) = _
  rw [map_smul, f.characterScaling_spec sx sy hx1 hy1 hxm hym hc p hdx hdy hsx hsy,
    ← hu, smul_smul, Units.inv_mul, one_smul]
  rfl

end ThreeAdicPlan

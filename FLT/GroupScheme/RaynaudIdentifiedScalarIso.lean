/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarModelIso
public import FLT.GroupScheme.RaynaudIdentifiedCharacters

/-!
# Scalar model rigidity through prescribed generic identifications

Transport the point-space module structure from the original model to both
identified models. Their integral scalar actions are the independently
constructed lifts of this transported action, so rank-one rigidity applies.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] {X M N : FF R K} [Module F X.Points]
  (fx : GenericGaloisHom X M) (fy : GenericGaloisHom X N)
  (hfx : Function.Bijective fx) (hfy : Function.Bijective fy)
  (f : ModelHom M N) (hf : Function.Bijective (genericHom f))
  (hident : (genericHom f).comp fx = fy)
  (sx : F → ModelHom M M) (sy : F → ModelHom N N)
  (hx0 : sx 0 = ModelHom.zero M M) (hy0 : sy 0 = ModelHom.zero N N)
  (hx1 : sx 1 = BialgHom.id R M.CoordinateRing)
  (hy1 : sy 1 = BialgHom.id R N.CoordinateRing)
  (hxm : ∀ a b, sx (a * b) = (sx b).comp (sx a))
  (hym : ∀ a b, sy (a * b) = (sy b).comp (sy a))
  (hxa : ∀ a b, sx (a + b) = (sx a).add (sx b))
  (hya : ∀ a b, sy (a + b) = (sy a).add (sy b))
  (hsx : ∀ a x, genericHom (sx a) (fx x) = fx (a • x))
  (hsy : ∀ a x, genericHom (sy a) (fy x) = fy (a • x))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)

include hfx hfy hf hident hx0 hy0 hx1 hy1 hxm hym hxa hya hsx hsy hdim in
/-- Actual identified rank-one scalar models agree below the small-ramification bound. -/
theorem ModelHom.bijective_of_identified_rank_one_scalars
    (he : RaynaudParameters.order (p : R) < p - 1) : Function.Bijective f := by
  let ex : M.Points ≃+ X.Points := (AddEquiv.ofBijective fx.toAddMonoidHom hfx).symm
  let ey : N.Points ≃+ X.Points := (AddEquiv.ofBijective fy.toAddMonoidHom hfy).symm
  let : Module F M.Points := ex.module F
  let : Module F N.Points := ey.module F
  have hdx : Module.finrank F M.Points = 1 := (ex.linearEquiv F).finrank_eq.trans hdim
  have hdy : Module.finrank F N.Points = 1 := (ey.linearEquiv F).finrank_eq.trans hdim
  have hsxm (a : F) (x : M.Points) : genericHom (sx a) x = a • x := by
    obtain ⟨z, rfl⟩ := hfx.surjective x
    rw [hsx]
    exact (ex.linearEquiv F).symm.map_smul a z
  have hsym (a : F) (y : N.Points) : genericHom (sy a) y = a • y := by
    obtain ⟨z, rfl⟩ := hfy.surjective y
    rw [hsy]
    exact (ey.linearEquiv F).symm.map_smul a z
  have hm (x : X.Points) : genericHom f (fx x) = fy x := DFunLike.congr_fun hident x
  have hlinear (a : F) (x : M.Points) : genericHom f (a • x) = a • genericHom f x := by
    obtain ⟨z, rfl⟩ := hfx.surjective x
    have hx : fx (a • z) = a • fx z := (ex.linearEquiv F).symm.map_smul a z
    rw [← hx]
    change genericHom f (fx (a • z)) = a • genericHom f (fx z)
    rw [hm, hm]
    exact (ey.linearEquiv F).symm.map_smul a z
  exact f.bijective_of_rank_one_scalars sx sy hx0 hy0 hx1 hy1 hxm hym hxa hya p hdx hdy
    hsxm hsym hf hlinear he

end ThreeAdicPlan

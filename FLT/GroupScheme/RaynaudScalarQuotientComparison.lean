/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRankOneScalarExtension
public import FLT.GroupScheme.RaynaudQuotientFunctoriality

/-!
# Rank-one rigidity for the actual quotient comparison

Both contracted quotients retain the prescribed quotient point group. Extend
its inverse identity map and use generic faithfulness to obtain an integral
inverse to the given comparison.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Finite F]
  {X X' Q : FF R K} [Module F Q.Points]
  [SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Q.Points]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]

/-- A comparison of quotients with the same rank-one scalar points is bijective. -/
theorem GenericGaloisHom.scalar_flatQuotientMap_bijective
    (q : GenericGaloisHom X Q) (q' : GenericGaloisHom X' Q)
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (g : ModelHom X X') (h : GenericGaloisHom Q Q) (hid : ∀ x, h x = x)
    (hc : q'.comp (genericHom g) = h.comp q)
    (hdim : Module.finrank F Q.Points = 1)
    (he : RaynaudParameters.order (p : R) < p - 1) :
    Function.Bijective (q.flatQuotientMap q' hq hq' g h hc) := by
  let : Module F (q'.flatQuotient hq').Points := inferInstanceAs (Module F Q.Points)
  let : SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (q'.flatQuotient hq').Points := inferInstanceAs
        (SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Q.Points)
  let f := q.flatQuotientMap q' hq hq' g h hc
  let inv : GenericGaloisHom (q'.flatQuotient hq') (q.flatQuotient hq) :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  obtain ⟨a, ha, _⟩ := extend_from_rank_one_scalar_model (F := F)
    (q'.flatQuotient hq') p hdim he (q.flatQuotient hq) inv
  have hfa : f.comp a = BialgHom.id R (q.flatQuotient hq).CoordinateRing := by
    apply genericHom_injective
    ext x
    rw [genericHom_comp, ha, genericHom_id]
    change genericHom f x = x
    exact (q.genericHom_flatQuotientMap q' hq hq' g h hc x).trans (hid x)
  have hsur : Function.Surjective h := fun x ↦ ⟨x, hid x⟩
  refine ⟨q.flatQuotientMap_injective q' hq hq' g h hc hsur, fun x ↦ ?_⟩
  exact ⟨a x, DFunLike.congr_fun hfa x⟩

end ThreeAdicPlan

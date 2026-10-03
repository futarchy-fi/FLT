/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudBiduality
public import FLT.GroupScheme.RaynaudMaximalExtension

/-!
# A minimal finite flat model by integral Cartier duality

Dualize the constructed maximum of the dual generic fibre. Every prescribed
generic map into this model extends, by transposing an extension out of the
maximum. No small-ramification theorem or presentation is used.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- The dual of a model with the universal outgoing extension property has the
universal incoming extension property. -/
theorem extend_into_dual_of_maximal (L : FF R K)
    (hL : ∀ (Z : FF R K) (q : GenericGaloisHom L Z), ∃! h : ModelHom L Z, genericHom h = q)
    (Y : FF R K) (g : GenericGaloisHom Y L.cartierDual) :
    ∃! h : ModelHom Y L.cartierDual, genericHom h = g := by
  let q := g.cartierDual.comp (genericHom L.toCartierBidual)
  obtain ⟨k, hk, -⟩ := hL Y.cartierDual q
  have hh : genericHom k.transpose = g := by
    apply GenericGaloisHom.cartierDual_injective
    rw [← ModelHom.genericHom_cartierDual]
    ext x
    obtain ⟨y, rfl⟩ := L.genericHom_toCartierBidual_bijective.2 x
    rw [← genericHom_comp, ModelHom.transpose_cartierDual, hk]
    rfl
  exact ⟨k.transpose, hh, fun h hh' ↦ genericHom_injective _ _ (hh'.trans hh.symm)⟩

/-- Construct a minimum with its specified generic identification and the actual
extension of every generic map into it. -/
theorem exists_minimal_model_extension (X : FF R K) :
    ∃ (M : FF R K) (f : GenericGaloisHom X M), Function.Bijective f ∧
      ∀ (Y : FF R K) (g : GenericGaloisHom Y M), ∃! h : ModelHom Y M, genericHom h = g := by
  obtain ⟨L, f, hf, hL⟩ := exists_maximal_model_extension X.cartierDual
  let d := f.cartierDual
  have hd := f.cartierDual_bijective hf
  let g := (d.inverse hd).comp (genericHom X.toCartierBidual)
  have hdi : Function.Bijective (d.inverse hd) :=
    (AddEquiv.ofBijective d.toAddMonoidHom hd).symm.bijective
  exact ⟨L.cartierDual, g, hdi.comp X.genericHom_toCartierBidual_bijective,
    extend_into_dual_of_maximal L hL⟩

/-- Every generic automorphism of the constructed minimum extends integrally. -/
theorem exists_minimal_model_automorphisms (X : FF R K) :
    ∃ (M : FF R K) (f : GenericGaloisHom X M), Function.Bijective f ∧
      ∀ g : GenericGaloisHom M M, Function.Bijective g →
        ∃ e : M.Iso M, genericHom e.toBialgHom = g := by
  obtain ⟨M, f, hf, hmin⟩ := exists_minimal_model_extension X
  refine ⟨M, f, hf, fun g hg ↦ ?_⟩
  obtain ⟨a, ha, -⟩ := hmin M g
  obtain ⟨b, hb, -⟩ := hmin M (g.inverse hg)
  have hab (x) : genericHom b (genericHom a x) = x := by
    rw [ha, hb, GenericGaloisHom.inverse_apply]
  have hba (x) : genericHom a (genericHom b x) = x := by
    obtain ⟨x, rfl⟩ := hg.2 x
    rw [ha, hb, GenericGaloisHom.inverse_apply]
  exact ⟨FF.isoOfGenericInverse a b hab hba, ha⟩

end ThreeAdicPlan

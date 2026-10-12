/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Grassmannian

/-!
# Selecting quotient bases from ambient generators over local rings

A finite projective quotient of rank d over a local ring has a basis given by
exactly d distinct members of any spanning family. The injection into the original
index set is retained; this is the input for reindexing an ambient basis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M Q ι : Type u} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]

/-- A spanning family of a finite projective module over a local ring contains a basis. -/
theorem exists_selected_basis_of_span [Module.Finite R Q] [Module.Projective R Q]
    (v : ι → Q) (hv : Submodule.span R (Set.range v) = ⊤)
    {d : ℕ} (hd : Module.finrank R Q = d) :
    ∃ (a : Fin d ↪ ι) (b : Module.Basis (Fin d) R Q), ∀ i, b i = v (a i) := by
  let _ := Module.finitePresentation_of_projective R Q
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  let _ : Finite κ := Module.Finite.finite_basis b
  have hc : Nat.card κ = d := (Module.finrank_eq_nat_card_basis b).symm.trans hd
  let e : κ ≃ Fin d := (Finite.equivFin κ).trans (finCongr hc)
  have ha : Function.Injective a := by
    intro i j hij
    apply b.injective
    rw [hb, hb, hij]
  refine ⟨⟨a ∘ e.symm, ha.comp e.symm.injective⟩, b.reindex e, ?_⟩
  intro i
  simpa only [Module.Basis.reindex_apply, Function.Embedding.coeFn_mk,
    Function.comp_apply] using hb (e.symm i)

omit [IsLocalRing R] in
/-- Surjective images of an ambient basis span the original quotient. -/
theorem span_quotient_basis (b : Module.Basis ι R M)
    (q : M →ₗ[R] Q) (hq : Function.Surjective q) :
    Submodule.span R (Set.range (fun i ↦ q (b i))) = ⊤ := by
  change Submodule.span R (Set.range (q ∘ b)) = ⊤
  rw [Set.range_comp, Submodule.span_image, b.span_eq,
    Submodule.map_top, LinearMap.range_eq_top.mpr hq]

/-- The selected quotient basis comes from distinct vectors of the given ambient basis. -/
theorem exists_selected_quotient_basis [Module.Finite R Q] [Module.Projective R Q]
    (b : Module.Basis ι R M) (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    {d : ℕ} (hd : Module.finrank R Q = d) :
    ∃ (a : Fin d ↪ ι) (c : Module.Basis (Fin d) R Q), ∀ i, c i = q (b (a i)) :=
  exists_selected_basis_of_span _ (span_quotient_basis b q hq) hd

end FLT.Mazur.GrassmannianChart

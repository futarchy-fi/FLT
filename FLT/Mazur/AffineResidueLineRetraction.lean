/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTildePullbackNonvanishing
public import FLT.Mazur.LineScalarExtensionNonvanishing
public import FLT.Mazur.ResiduePullbackNonvanishingTransport

/-!
# Affine sheaf retractions from actual residue nonvanishing

A map with a scalar source and free ambient module splits when every actual
scheme residue pullback is nonzero. The retraction is obtained over the original
ring and reconstructed through tilde, with arbitrary source and ambient charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (comp_zero zero_comp)
open Scheme.Modules
namespace FLT.Mazur.AffineResidueLineRetraction
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : CommRingCat.{u}} {M : ModuleCat.{u} R} {ι : Type u}
  (b : Module.Basis ι R M)

include b

/-- Actual residue nonvanishing splits a tilde line map over the original affine scheme. -/
lemma exists_tilde_retraction (f : ModuleCat.of R R ⟶ M)
    (h : ∀ p : Spec R, (pullback ((Spec R).fromSpecResidueField p)).map
      ((tilde.functor R).map f) ≠ 0) :
    ∃ r : tilde M ⟶ tilde (ModuleCat.of R R), (tilde.functor R).map f ≫ r = 𝟙 _ := by
  obtain ⟨r, hr⟩ := LineScalarExtensionNonvanishing.exists_retraction f b (fun p ↦
    (AffineTildePullbackNonvanishing.map_ne_zero_iff _ f).mp
      (ResiduePullbackNonvanishingTransport.ideal_residue_map_ne_zero _ p (h p)))
  exact ⟨(tilde.functor R).map r, by rw [← Functor.map_comp, hr, CategoryTheory.Functor.map_id]⟩

/-- Simultaneous source and ambient affine charts transport the constructed retraction. -/
lemma exists_retraction {L N : (Spec R).Modules} (s : L ⟶ N)
    (eL : tilde (ModuleCat.of R R) ≅ L) (eN : tilde M ≅ N)
    (h : ∀ p : Spec R, (pullback ((Spec R).fromSpecResidueField p)).map s ≠ 0) :
    ∃ r : N ⟶ L, s ≫ r = 𝟙 L := by
  let f := (tilde.functor R).preimage (eL.hom ≫ s ≫ eN.inv)
  have hf : (tilde.functor R).map f = eL.hom ≫ s ≫ eN.inv :=
    (tilde.functor R).map_preimage _
  obtain ⟨r, hr⟩ := exists_tilde_retraction b f (fun p ↦ by
    rw [hf]
    intro hz
    apply h p
    apply (cancel_epi ((pullback ((Spec R).fromSpecResidueField p)).map eL.hom)).mp
    apply (cancel_mono ((pullback ((Spec R).fromSpecResidueField p)).map eN.inv)).mp
    simpa only [Functor.map_comp, Category.assoc, comp_zero, zero_comp] using hz)
  refine ⟨eN.inv ≫ r ≫ eL.hom, ?_⟩
  apply (cancel_epi eL.hom).mp
  rw [Category.comp_id]
  rw [hf] at hr
  simpa only [Category.assoc, Category.id_comp] using congrArg (fun k ↦ k ≫ eL.hom) hr

end FLT.Mazur.AffineResidueLineRetraction

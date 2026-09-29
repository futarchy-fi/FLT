/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingDescent
public import FLT.Mazur.CechConnecting

/-!
# Sectionwise exact Cech sequences

A short exact coefficient sequence induces a short exact Cech sequence whenever
the quotient map is surjective on sections of every cover intersection.
The hypothesis concerns only sections, so this construction can be used before
any higher cohomology vanishing has been established.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace FLT.Mazur.AffineCohomologyVanishingCechSequence

open CechSheafHZero CechAcyclicCokernel AffineCohomologyVanishingDescent CechConnecting

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Sectionwise surjectivity on intersections gives surjectivity of a Cech term map. -/
lemma termMap_surjective {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ)
    (hf : ∀ a : Fin (n + 1) → ι, Function.Surjective (f.hom.app (op (V U n a)))) :
    Function.Surjective (termMap U f n) := by
  intro s
  have hlift (a : Fin (n + 1) → ι) :
      ∃ t, f.hom.app (op (V U n a)) t = termEquiv U G n s a := hf a _
  choose t ht using hlift
  refine ⟨(termEquiv U F n).symm t, ?_⟩
  apply (termEquiv U G n).injective
  funext a
  rw [termEquiv_naturality, AddEquiv.apply_symm_apply]
  exact ht a

/-- Exact coefficient sections make the induced sequence short exact in each degree. -/
lemma cech_degree_shortExact_of_sections
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    (hg : ∀ a : Fin (n + 1) → ι,
      Function.Surjective (S.g.hom.app (op (V U n a)))) :
    ((cechShortComplex U S).map
      (HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n)).ShortExact := by
  have := hS.mono_f
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (ShortComplex.ab_exact_iff_function_exact _).mpr (termMap_exact U hS n)
  · exact (AddCommGrpCat.mono_iff_injective _).mpr (termMap_injective U S.f n)
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr (termMap_surjective U S.g n hg)

/-- Sectionwise surjectivity makes the Cech sequence short exact for an arbitrary family. -/
lemma cechShortComplex_shortExact_of_sections
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (hg : ∀ (n : ℕ) (a : Fin (n + 1) → ι),
      Function.Surjective (S.g.hom.app (op (V U n a)))) :
    (cechShortComplex U S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact cech_degree_shortExact_of_sections U hS n (hg n)

end FLT.Mazur.AffineCohomologyVanishingCechSequence

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSubgroupComparison
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fppf-local cyclicity of finite subgroups

Cyclicity means that a Cartier generator exists after a faithfully flat,
locally finitely presented cover. The actual generator condition preserves
multiplicities. Cyclicity is stable under arbitrary base change and descends
along any such cover; no descent conclusion is a field of a record.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n)

/-- Fppf-local existence of a Cartier generator for the actual subgroup divisor. -/
def IsCyclic : Prop := ∃ (U : Scheme) (g : U ⟶ S),
  Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
    ∃ P, (H.baseChange g).IsCartierGenerator P

/-- A global Cartier generator in particular gives a cyclic subgroup. -/
theorem IsCartierGenerator.isCyclic {P : MonoidalCategory.tensorUnit (Over S) ⟶ H.carrier}
    (hP : H.IsCartierGenerator P) : H.IsCyclic :=
  ⟨S, 𝟙 S, inferInstance, inferInstance, inferInstance,
    H.exists_generator_id_iff.mpr ⟨P, hP⟩⟩

/-- Cyclicity survives arbitrary, possibly nonflat and nonreduced, base change. -/
theorem IsCyclic.baseChange (hH : H.IsCyclic) (f : T ⟶ S) : (H.baseChange f).IsCyclic := by
  obtain ⟨U, g, hg, hs, hl, P, hP⟩ := hH
  let := hg
  let := hs
  let := hl
  refine ⟨pullback g f, pullback.snd g f, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← H.exists_generator_comp_iff, ← pullback.condition, H.exists_generator_comp_iff]
  exact ⟨_, hP.baseChange _ (pullback.fst g f)⟩

/-- Cyclicity descends along a faithfully flat locally finitely presented cover. -/
theorem IsCyclic.of_baseChange (f : T ⟶ S) [Flat f] [Surjective f]
    [LocallyOfFinitePresentation f] (hH : (H.baseChange f).IsCyclic) : H.IsCyclic := by
  obtain ⟨U, g, hg, hs, hl, P, hP⟩ := hH
  let := hg
  let := hs
  let := hl
  exact ⟨U, g ≫ f, inferInstance, inferInstance, inferInstance,
    (H.exists_generator_comp_iff f g).mpr ⟨P, hP⟩⟩

/-- The cyclic condition is fppf local on the base. -/
theorem isCyclic_baseChange_iff (f : T ⟶ S) [Flat f] [Surjective f]
    [LocallyOfFinitePresentation f] : (H.baseChange f).IsCyclic ↔ H.IsCyclic :=
  ⟨IsCyclic.of_baseChange H f, fun h ↦ h.baseChange H f⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationPrincipalSpectrum
public import FLT.Mazur.SchemeRelationInvariantTestEquality

/-!
# Original invariant kernel tests on principal sources

Localization compares the entire kernel on an invariant principal source with
its old invariant coefficient map. This remains true for a newly constructed
relation identified with the full two-endpoint restriction. No effectiveness
or representative hypothesis is required, and arbitrary scheme tests are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationPrincipalLocalization
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A) (s : compatibleFunctions p q)
  [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace D] [QuasiSeparatedSpace D]
local notation "W" => A.basicOpen s.val
local notation "p'" => SchemeRelationRestriction.fst p q (Scheme.Opens.ι W)
local notation "q'" => SchemeRelationRestriction.snd p q (Scheme.Opens.ι W)

/-- The full principal relation detects exactly the old invariant coefficient kernel. -/
theorem principal_projection_test_iff {T : Scheme.{u}} (a b : T ⟶ (W).toScheme) :
    a ≫ projection p' q' = b ≫ projection p' q' ↔
      a ≫ (W).ι ≫ projection p q = b ≫ (W).ι ≫ projection p q := by
  rw [← cancel_mono (candidateOpenMap p q s)]
  simp only [Category.assoc, candidateOpenMap_projection]

/-- Recomputing the full relation does not change the principal source's old kernel tests. -/
theorem recomputed_projection_test_iff {E : Scheme.{u}} (r t : E ⟶ (W).toScheme)
    (e : E ≅ SchemeRelationRestriction.doubleDomain p q (W).ι)
    (hr : e.hom ≫ p' = r) (ht : e.hom ≫ q' = t)
    {T : Scheme.{u}} (a b : T ⟶ (W).toScheme) :
    a ≫ projection r t = b ≫ projection r t ↔
      a ≫ (W).ι ≫ projection p q = b ≫ (W).ι ≫ projection p q := by
  have h := relationIso_compatibleFunctions p' q' r t e hr ht
  rw [← principal_projection_test_iff p q s a b]
  rw [projection_test_eq_iff, projection_test_eq_iff]
  constructor
  · intro H z
    exact H ⟨z.val, h ▸ z.property⟩
  · intro H z
    exact H ⟨z.val, h.symm ▸ z.property⟩

end FLT.Mazur.SchemeRelationPrincipalLocalization

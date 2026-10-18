/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupGeneratorMarking

/-!
# Detecting full compatible comparisons by their smooth-group maps

When the source smooth inclusion is an epimorphism, its group map determines
the whole curve map. The target subgroup inclusion then determines the
subgroup map, so the entire compatible comparison is determined.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- A full compatible comparison is determined by its group map on an epimorphic smooth locus. -/
theorem CompatibleIso.eq_of_group [Epi E.inclusion] (a b : CompatibleIso H J)
    (h : a.curve.hom.group = b.curve.hom.group) : a = b := by
  apply CompatibleIso.ext
  · apply Iso.ext
    apply Hom.ext _ h
    apply (cancel_epi E.inclusion).mp
    rw [a.curve.hom.inclusion, b.curve.hom.inclusion, h]
  · apply Iso.ext
    let _ : Mono J.inclusion := Over.mono_of_mono_left J.inclusion
    apply (cancel_mono J.inclusion).mp
    rw [← a.group_inclusion, ← b.group_inclusion, h]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineSheafDescent
public import FLT.Mazur.AmpleFiberCartesianDescent

/-!
# Proper Noetherian models retaining an ample fiber

For a proper finitely presented family with an invertible sheaf and a chosen
ample fiber, the finite integer coefficient model is proper and its fiber
at the contracted point is ample. The latter follows from the cartesian
fiber square and fpqc descent over the residue-field extension.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.Approximation

/-- Descend the family, invertible sheaf, and ampleness of a specified fiber
simultaneously, retaining any prescribed finite set of coefficients. -/
theorem exists_proper_ample_fiber_model {A : Type} [CommRing A]
    {X : Scheme} (p : X ⟶ Spec (.of A)) [IsProper p] [LocallyOfFinitePresentation p]
    (L : X.Modules) (hL : LocallyFreeRankOne L) (x : Spec (.of A))
    (hA : RelativeAmple (p.fiberToSpecResidueField x)
      ((Scheme.Modules.pullback (p.fiberι x)).obj L)) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ (Y : Scheme) (q : Y ⟶ Spec (.of S)) (M : Y.Modules),
        IsProper q ∧ LocallyOfFinitePresentation q ∧ IsNoetherian Y ∧
        LocallyFreeRankOne M ∧ ∃ a : X ⟶ Y,
          IsPullback a p q (Spec.map (CommRingCat.ofHom (algebraMap S A))) ∧
          Nonempty ((Scheme.Modules.pullback a).obj M ≅ L) ∧
          RelativeAmple (q.fiberToSpecResidueField
            (Spec.map (CommRingCat.ofHom (algebraMap S A)) x))
            ((Scheme.Modules.pullback (q.fiberι
              (Spec.map (CommRingCat.ofHom (algebraMap S A)) x))).obj M) := by
  obtain ⟨S, hS, hsS, Y, q, M, hq, hfp, hM, a, ha, ⟨e⟩⟩ :=
    exists_proper_finite_presentation_line_sheaf_descent p L hL s hs
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  refine ⟨S, hS, hsS, Y, q, M, hq, hfp, ⟨⟩, hM, a, ha, ⟨e⟩, ?_⟩
  exact relativeAmple_fiber_of_isPullback ha hM x
    (hA.of_iso ((Scheme.Modules.pullback (p.fiberι x)).mapIso e))

end FLT.Mazur.Approximation

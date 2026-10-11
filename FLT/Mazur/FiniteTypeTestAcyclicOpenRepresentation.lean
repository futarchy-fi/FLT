/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestAcyclicOpen

/-!
# The intrinsic test-line open represents all further cartesian tests

The representing open commutes with arbitrary further base change, without
Noetherian restrictions. Its definition is independent of any original model.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- Independent original models yield exactly the same open, not just isomorphic opens. -/
theorem finiteTypeTestAcyclicOpen_model_independent
    {R' : Type} [CommRing R'] [Algebra.FiniteType ℤ R']
    {Y' : Scheme.{0}} {a' : X ⟶ Y'} {q' : Y' ⟶ Spec (.of R')}
    [IsProper q'] [Flat q'] [GeometricallyIntegral q']
    {g' : S ⟶ Spec (.of R')} (h' : IsPullback a' f q' g') :
    finiteTypeTestAcyclicOpen h L hL = finiteTypeTestAcyclicOpen h' L hL := rfl

variable {P T : Scheme.{0}} {p : P ⟶ X} {r : P ⟶ T} {b : T ⟶ S}
  (H : IsPullback p r f b)

/-- The actual open commutes with every further cartesian test map. -/
theorem finiteTypeTestAcyclicOpen_baseChange :
    finiteTypeTestAcyclicOpen (H.paste_horiz h) ((pullback p).obj L) (hL.pullback p) =
      b ⁻¹ᵁ finiteTypeTestAcyclicOpen h L hL := by
  let _ : IsProper f := MorphismProperty.of_isPullback h inferInstance
  exact SetLike.coe_injective (geometricAcyclicRankOneLocus_baseChange f H L hL)

include H in
/-- Unique factorization into the open is precisely geometric acyclic rank one on the test. -/
theorem finiteTypeTestAcyclicOpen_represents :
    GeometricAcyclicRankOne r ((pullback p).obj L) ↔
      ∃! k : T ⟶ (finiteTypeTestAcyclicOpen h L hL).toScheme,
        k ≫ (finiteTypeTestAcyclicOpen h L hL).ι = b := by
  let _ : IsProper f := MorphismProperty.of_isPullback h inferInstance
  have hm : GeometricAcyclicRankOne r ((pullback p).obj L) ↔
      ∀ t : T, b t ∈ finiteTypeTestAcyclicOpen h L hL :=
    forall_congr' fun t ↦ Set.ext_iff.mp
      (geometricAcyclicRankOneLocus_baseChange f H L hL) t
  rw [hm]
  constructor
  · intro ht
    have hr : Set.range b ⊆ Set.range (finiteTypeTestAcyclicOpen h L hL).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      exact ht t
    refine ⟨IsOpenImmersion.lift _ b hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    intro k hk
    rw [← cancel_mono (finiteTypeTestAcyclicOpen h L hL).ι, hk, IsOpenImmersion.lift_fac]
  · rintro ⟨k, hk, _⟩ t
    rw [← hk]
    exact (k t).property

end FLT.Mazur.CartierAbel

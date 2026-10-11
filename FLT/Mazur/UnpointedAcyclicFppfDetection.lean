/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFppfComparisonCover
public import FLT.Mazur.GeometricAcyclicFppfLocus

/-!
# The Picard sheaf detects acyclicity without an original section

Equality in the actual sheaf supplies a jointly surjective fppf family of
equal relative classes. Geometric acyclicity descends along this family.
This does not assert that arbitrary sheaf sections have global representatives.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f]

/-- Equal actual Picard-sheaf sections have the same geometric acyclic condition. -/
theorem relativeGeometricAcyclicRankOne_of_fppfClass_eq (T : Over S)
    (a b : RelativePic (Limits.pullback.snd f T.hom))
    (hab : relativeFppfClass f T a = relativeFppfClass f T b) :
    RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.hom) a ↔
      RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.hom) b := by
  obtain ⟨𝒰, h𝒰⟩ := relativeFppfClass_eq_exists_cover f T a b hab
  rw [relativeGeometricAcyclicRankOne_fppf_iff f T 𝒰 a,
    relativeGeometricAcyclicRankOne_fppf_iff f T 𝒰 b]
  exact forall_congr' fun i ↦ by rw [h𝒰 i]

/-- The actual represented acyclic image detects each class without a pointed hypothesis. -/
theorem unpointed_geometricAcyclicFppf_class_iff (T : Over S)
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    relativeFppfClass f T c ∈ (geometricAcyclicFppfSubfunctor f).obj (op T) ↔
      RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.hom) c := by
  constructor
  · rintro ⟨d, hd, hdc⟩
    exact (relativeGeometricAcyclicRankOne_of_fppfClass_eq f T d c hdc).mp hd
  · intro hc
    exact ⟨c, hc, rfl⟩

end FLT.Mazur.CartierAbel

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalClosedFiberTensorComplex

/-!
# Arbitrary affine base change from one local closed fiber

For a pointed proper flat family with geometrically reduced fibers over a
Noetherian local affine base, the connected closed fiber controls actual
functions after every affine base change. The new base need not be local,
Noetherian, flat, or reduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.LocalClosedFiberUniversalFunctions
open Approximation ArtinianProperAffineBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)] [IsAffine T]
  [IsProper f] [Flat f] [GeometricallyReduced f]
  (hc : S.isoSpec.inv (IsLocalRing.closedPoint Γ(S, ⊤)) ∈ geometricallyConnectedLocus f)

include h s hs hc

/-- Every affine base change has exactly its base functions, using only the local closed fiber. -/
theorem appTop_bijective : Function.Bijective q.appTop := by
  let _ : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let _ := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i ↦ (C.f i).opensRange
  have hA (i : C.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (C.f i)
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  have he := LocalClosedFiberTensorComplex.cover_exact f s hs hc U C.iSup_opensRange hA Γ(T, ⊤)
  have hsurj := CartesianStructureComplexGluing.appTop_surjective_of_exact h U
    C.iSup_opensRange hA (fun i j ↦ (hA i).inf (hA j)) he
  have hleft : Function.LeftInverse (sectionOfSquare h s hs).appTop q.appTop :=
    SchemeRelativeNilpotentSections.evaluation_pullback q (sectionOfSquare h s hs)
      (sectionOfSquare_projection h s hs)
  exact ⟨hleft.injective, hsurj⟩

/-- The original evaluation remains injective under arbitrary affine change of base. -/
theorem evaluation_injective : Function.Injective (sectionOfSquare h s hs).appTop := by
  have H := appTop_bijective h s hs hc
  have he := SchemeRelativeNilpotentSections.evaluation_pullback q (sectionOfSquare h s hs)
    (sectionOfSquare_projection h s hs)
  intro x y hxy
  obtain ⟨a, rfl⟩ := H.surjective x
  obtain ⟨b, rfl⟩ := H.surjective y
  rw [he, he] at hxy
  exact congrArg q.appTop hxy

end FLT.Mazur.LocalClosedFiberUniversalFunctions

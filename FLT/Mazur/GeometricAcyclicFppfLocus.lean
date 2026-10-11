/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricAcyclicPicardLocality
public import FLT.Mazur.ProperPointedRelativeFppfIso

/-!
# The geometric acyclic locus in the actual fppf Picard sheaf

Membership means having an actual relative line class with the geometric
acyclic rank-one property. For proper pointed families the comparison
identifies this image with the intrinsic relative Picard subfunctor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f]

/-- The image locus retains the canonical class map into the actual Picard sheaf. -/
def geometricAcyclicFppfSubfunctor :
    Subfunctor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat) where
  obj T := {s | ∃ c, RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.unop.hom) c ∧
    relativeFppfClass f T.unop c = s}
  map g _ hs := by
    obtain ⟨c, hc, rfl⟩ := hs
    exact ⟨relativeBaseMap f g.unop c,
      relativeGeometricAcyclicRankOne_map _ (relativeTotalMap_isPullback f g.unop) hc,
      (relativeFppfClass_naturality f g.unop c).symm⟩

variable (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  [IsLocallyNoetherian S] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]

include e he in
/-- For proper pointed families the comparison detects the intrinsic acyclic condition. -/
theorem geometricAcyclicFppf_class_iff (T : Over S)
    (c : RelativePic (Limits.pullback.snd f T.hom)) :
    relativeFppfClass f T c ∈ (geometricAcyclicFppfSubfunctor f).obj (op T) ↔
      RelativeGeometricAcyclicRankOne (Limits.pullback.snd f T.hom) c := by
  constructor
  · rintro ⟨d, hd, hdc⟩
    have h := (properPointedRelativeFppfEquiv f e he T).injective hdc
    exact h ▸ hd
  · intro hc
    exact ⟨c, hc, rfl⟩

/-- The acyclic locus comparison on each arbitrary test scheme. -/
def geometricAcyclicFppfEquiv (T : Over S) :
    (geometricAcyclicPicardSubfunctor f).toFunctor.obj (op T) ≃
      (geometricAcyclicFppfSubfunctor f).toFunctor.obj (op T) where
  toFun c := ⟨relativeFppfClass f T c.val, c.val, c.property, rfl⟩
  invFun s := ⟨(properPointedRelativeFppfEquiv f e he T).symm s.val, by
    apply (geometricAcyclicFppf_class_iff f e he T _).mp
    change properPointedRelativeFppfEquiv f e he T
      ((properPointedRelativeFppfEquiv f e he T).symm s.val) ∈ _
    rw [Equiv.apply_symm_apply]
    exact s.property⟩
  left_inv c := Subtype.ext ((properPointedRelativeFppfEquiv f e he T).symm_apply_apply c.val)
  right_inv s := Subtype.ext ((properPointedRelativeFppfEquiv f e he T).apply_symm_apply s.val)

/-- The pointwise comparisons commute with every actual restriction map. -/
def geometricAcyclicFppfIso :
    (geometricAcyclicPicardSubfunctor f).toFunctor ≅
      (geometricAcyclicFppfSubfunctor f).toFunctor :=
  NatIso.ofComponents (fun T ↦ (geometricAcyclicFppfEquiv f e he T.unop).toIso)
    (fun {T U} g ↦ by
      apply ConcreteCategory.hom_ext
      intro c
      exact Subtype.ext (relativeFppfClass_naturality f g.unop c.val).symm)

end FLT.Mazur.CartierAbel

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchematicDescentGluing
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Locality of descent in the parameter scheme

A surjective schematically dominant normalization allows local pushout
descents over an open cover of the base to glue to a unique over-morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.OverPullbackLocalPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T U : Scheme.{u}} (g : U ⟶ T) {A P : Over T} (p : A ⟶ P)
theorem map_isPullback : IsPullback ((Over.pullback g).map p).left
    (pullback.fst A.hom g) (pullback.fst P.hom g) p.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd P.hom g) (h₂₂ := P.hom)
  · simpa [Over.pullback] using (IsPullback.of_hasPullback A.hom g).flip
  · simp [Over.pullback]
  · exact (IsPullback.of_hasPullback P.hom g).flip
variable {B D : Over T} (a : B ⟶ A) (b : B ⟶ D) (q : D ⟶ P)
  (w : a ≫ p = b ≫ q) (V : T.OpenCover)
  (h : ∀ i, IsPushout ((Over.pullback (V.f i)).map a) ((Over.pullback (V.f i)).map b)
    ((Over.pullback (V.f i)).map p) ((Over.pullback (V.f i)).map q))
include h in
theorem exists_desc [Surjective p.left] [QuasiCompact p.left]
    [IsSchemeTheoreticallyDominant p.left] {Y : Over T}
    (f : A ⟶ Y) (k : D ⟶ Y) (hf : a ≫ f = b ≫ k) :
    ∃! d : P ⟶ Y, p ≫ d = f := by
  let localDesc (i : V.I₀) := (h i).desc ((Over.pullback (V.f i)).map f)
    ((Over.pullback (V.f i)).map k) (by rw [← Functor.map_comp, ← Functor.map_comp, hf])
  let u (i : V.I₀) : pullback P.hom (V.f i) ⟶ Y.left :=
    (localDesc i).left ≫ pullback.fst Y.hom (V.f i)
  have hu (i : V.I₀) : ((Over.pullback (V.f i)).map p).left ≫ u i =
      pullback.fst A.hom (V.f i) ≫ f.left := by
    change ((Over.pullback (V.f i)).map p).left ≫
      (localDesc i).left ≫ pullback.fst Y.hom (V.f i) = _
    rw [← Category.assoc, ← Over.comp_left]
    dsimp only [localDesc]
    rw [IsPushout.inl_desc]
    simp [Over.pullback]
  obtain ⟨d, hd, huniq⟩ := SchematicDescentGluing.exists_desc_of_cover p.left f.left
    (V.pullback₁ P.hom) u (fun i ↦ by
      change pullback.fst p.left (pullback.fst P.hom (V.f i)) ≫ f.left =
        pullback.snd p.left (pullback.fst P.hom (V.f i)) ≫ u i
      apply (cancel_epi (map_isPullback (V.f i) p).flip.isoPullback.hom).mp
      simp only [IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc]
      exact (hu i).symm)
  let : Epi p.left := SurjectiveDominantEpi.epi _
  have hb : d ≫ Y.hom = P.hom := by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, hd, Over.w, Over.w]
  refine ⟨Over.homMk d hb, ?_, ?_⟩
  · exact Over.OverMorphism.ext hd
  · intro e he
    apply Over.OverMorphism.ext
    exact huniq e.left (congrArg Over.Hom.left he)
end FLT.Mazur.OverPullbackLocalPushout

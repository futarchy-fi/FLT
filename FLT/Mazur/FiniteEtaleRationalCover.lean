/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.FiniteEtaleFiniteFieldCover

/-!
# Rational sections on the canonical finite field base change

Transport the constructed cover along its Cartesian comparison. The resulting
family lives on the canonical pullback of the original scheme itself.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleRationalCover
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  [Etale f] [IsFinite f]

/-- The canonical base change has finitely many actual rational sections covering every point. -/
theorem exists_cover :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
      (_j : L →ₐ[k] AlgebraicClosure k) (n : ℕ)
      (r : Fin n → (Spec (.of L) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))))),
      (∀ a, r a ≫ pullback.snd f _ = 𝟙 _) ∧
      (∀ a, IsOpenImmersion (r a)) ∧
      (∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme),
        ∃ a z, r a z = x) := by
  obtain ⟨L, hL, aL, finL, j, n, E, h, p, s, H, _, _, hs, hi, hc⟩ :=
    FiniteEtaleFiniteFieldCover.exists_cover f
  let _ := hL
  let _ := aL
  let _ := finL
  let _ (a : Fin n) := hi a
  refine ⟨L, hL, aL, finL, j, n, fun a ↦ s a ≫ H.isoPullback.hom,
    fun a ↦ ?_, fun a ↦ inferInstance, ?_⟩
  · rw [Category.assoc, H.isoPullback_hom_snd, hs]
  · intro x
    obtain ⟨y, rfl⟩ := H.isoPullback.hom.surjective x
    obtain ⟨a, ha⟩ := hc y
    exact ⟨a, p y, congrArg H.isoPullback.hom ha⟩

end FLT.Mazur.FiniteEtaleRationalCover

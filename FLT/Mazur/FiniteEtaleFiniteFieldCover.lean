/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.FiniteEtaleGeometricSectionCover
public import FLT.Mazur.AlgebraicPointFiniteDescent
public import FLT.Mazur.SectionCoverBaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A finite field extension covering the original finite étale scheme by sections

Descend the geometric point on a splitting neighborhood to a finite residue
extension, then pull back its full section cover. The Cartesian square retains
exactly the original finite étale scheme, including every conjugate branch.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleFiniteFieldCover
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  [Etale f] [IsFinite f]

/-- A finite extension constructs a full rational section cover of the exact base change. -/
theorem exists_cover :
    ∃ (L : Type) (_ : Field L) (_ : Algebra k L) (_ : Module.Finite k L)
      (_j : L →ₐ[k] AlgebraicClosure k) (n : ℕ) (E : Scheme)
      (h : E ⟶ X) (p : E ⟶ Spec (.of L)) (r : Fin n → (Spec (.of L) ⟶ E)),
      IsPullback h p f (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
      IsFinite p ∧ Etale p ∧ (∀ a, r a ≫ p = 𝟙 _) ∧
      (∀ a, IsOpenImmersion (r a)) ∧ (∀ x : E, ∃ a, r a (p x) = x) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  obtain ⟨n, U, E, q, z, h, p, s, hU, hq, _, hz, H, hp, he, hs, _, hc⟩ :=
    FiniteEtaleGeometricSectionCover.exists_cover f b
  let _ := hq
  let _ := hp
  let _ := he
  obtain ⟨L, hL, aL, finL, j, g, hg, _⟩ :=
    AlgebraicPointFiniteDescent.exists_finite_factor q z hz
  let _ := hL
  let _ := aL
  let _ := finL
  let r (a : Fin n) := SectionCoverBaseChange.sectionMap p g (s a) (hs a)
  have hr (a : Fin n) : r a ≫ pullback.snd p g = 𝟙 _ :=
    SectionCoverBaseChange.sectionMap_snd p g (s a) (hs a)
  refine ⟨L, hL, aL, finL, j, n, pullback p g, pullback.fst p g ≫ h,
    pullback.snd p g, r, ?_, inferInstance, inferInstance, hr,
    fun a ↦ UnramifiedSectionImmersion.isOpenImmersion _ _ (hr a),
    SectionCoverBaseChange.covers p g s hs hc⟩
  rw [← hg]
  exact (IsPullback.of_hasPullback p g).paste_horiz H

end FLT.Mazur.FiniteEtaleFiniteFieldCover

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationFppfOrbitComparison
public import FLT.Mazur.RelativeRelationInvariantSectionRings
public import FLT.Mazur.RelativeRelationFpqcSectionComparison
public import FLT.Mazur.SchemeOpenSectionDescent

/-!
# Original invariant sections of fppf kernel pairs

On every target open, the invariant orbit sheaf has exactly the original
scheme's regular functions, without a quasi-compactness assumption. The comparison
is the actual locally ringed quotient map, with the change of open domains retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U T : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (g : U ⟶ T)
  (H : IsPullback p q g g) (W : T.left.Opens)

variable [Flat g.left] [LocallyOfFinitePresentation g.left] [Surjective g.left]

/-- The actual scheme section ring is the full original relation's compatible-function ring. -/
def fppfOriginalInvariantSectionsEquiv : Γ(T.left, W) ≃+*
    originalInvariantSections (p := p) (q := q) (g.left ⁻¹ᵁ W)
      (kernelPair_preimage_open (H.map (Over.forget S)) W) := by
  let φ := (g.left.app W).hom.codRestrict
    (originalInvariantSections (p := p) (q := q) (g.left ⁻¹ᵁ W)
      (kernelPair_preimage_open (H.map (Over.forget S)) W)) (fun t ↦ by
        have hh : g.left.app W ≫ p.left.app (g.left ⁻¹ᵁ W) =
            g.left.app W ≫ q.left.appLE (g.left ⁻¹ᵁ W)
              (p.left ⁻¹ᵁ (g.left ⁻¹ᵁ W))
              (kernelPair_preimage_open (H.map (Over.forget S)) W).le := by
          rw [g.left.app_eq_appLE, p.left.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
            Scheme.Hom.appLE_comp_appLE]
          congr 1
          exact congrArg Over.Hom.left H.w
        exact congrArg (fun k ↦ k t) hh)
  apply RingEquiv.ofBijective φ
  constructor
  · intro s t h
    exact app_injective W (congrArg Subtype.val h)
  · intro s
    obtain ⟨t, ht, _⟩ := app_existsUnique (g := g.left)
      (a := p.left) (b := q.left) (H.map (Over.forget S)) W s.val s.property
    exact ⟨t, Subtype.ext ht⟩

/-- The invariant sheaf on a comparison inverse image equals the original target section ring. -/
def fppfInvariantSectionsEquiv :
    (invariantSheaf e).obj.obj
        (op ((Opens.map (kernelQuotientComparison e g H).base).obj W)) ≃+* Γ(T.left, W) :=
  (invariantSectionRingEquivOn e _ _ (kernelQuotientComparison_preimage e g H W)
    (kernelPair_preimage_open (H.map (Over.forget S)) W)).trans
    (fppfOriginalInvariantSectionsEquiv g H W).symm

/-- Pulling back a target function through the actual quotient comparison recovers that function. -/
theorem fppfInvariantSectionsEquiv_comparison (s : Γ(T.left, W)) :
    fppfInvariantSectionsEquiv e g H W ((kernelQuotientComparison e g H).c.app (op W) s) =
      s := by
  apply (fppfOriginalInvariantSectionsEquiv g H W).injective
  rw [fppfInvariantSectionsEquiv, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [invariantSectionRingEquivOn_val]
  have hc : toRingedSpace e ≫ (kernelQuotientComparison e g H).toShHom =
      g.left.toShHom := by
    rw [← invariantLocallyRingedProjection_toShHom]
    exact congrArg (fun k ↦ k.toShHom) (kernelQuotientComparison_projection e g H)
  have h := PresheafedSpace.congr_app (congrArg (fun k ↦ k.hom) hc) (op W)
  change (kernelQuotientComparison e g H).c.app (op W) ≫
    (invariantInclusion e).hom.app _ = _ at h
  have hh := congrArg (fun k ↦ k s) h
  change U.left.presheaf.map _
    (((kernelQuotientComparison e g H).c.app (op W) ≫
      (invariantInclusion e).hom.app _) s) = g.left.app W s
  rw [hh]
  have he : U.left.presheaf.map (eqToHom (congrArg op
      (kernelQuotientComparison_preimage e g H W).symm)) ≫
      U.left.presheaf.map (eqToHom (congrArg op
        (kernelQuotientComparison_preimage e g H W))) = 𝟙 _ := by
    rw [← Functor.map_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  exact congrArg (fun k ↦ k (g.left.app W s)) he

end FLT.Mazur.RelativeRelationOrbit

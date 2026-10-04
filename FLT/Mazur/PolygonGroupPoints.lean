/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentUnitPoints
public import FLT.Mazur.PolygonActionTranslation
public import FLT.Mazur.OverCoproductModuleSections

/-!
# All rational points of the polygon smooth group

Every point factors through one Laurent component. Full faithfulness of Spec
and the Laurent units equivalence identify its coordinate with a unit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped LaurentPolynomial
universe u
namespace FLT.Mazur.PolygonGroupPoints
open PolygonActionTranslation
variable (K : Type u) [Field K]

/-- Every rational point of the multiplicative group is evaluation at a unit. -/
theorem gmPoint_surjective : Function.Surjective (gmPoint K) := by
  intro x
  let φ := Spec.preimage x.left
  have he : Spec.map φ = x.left := Spec.map_preimage _
  have hc' : CommRingCat.ofHom (algebraMap K K[T;T⁻¹]) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id]
    change Spec.map φ ≫ (MultiplicativeGroupScheme.gm K).hom = 𝟙 _
    rw [he]
    exact x.w
  have hc := congrArg CommRingCat.Hom.hom hc'
  let ψ : K[T;T⁻¹] →ₐ[K] K :=
    { __ := φ.hom
      commutes' := fun r ↦ congrArg (fun f : K →+* K ↦ f r) hc }
  refine ⟨LaurentUnitPoints.pointUnit ψ, ?_⟩
  apply Over.OverMorphism.ext
  rw [← he]
  change Spec.map _ = Spec.map φ
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (LaurentUnitPoints.evalUnit_pointUnit ψ)

/-- Every rational point of the split group has unit and component coordinates. -/
theorem groupPoint_surjective (n : ℕ)
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ ∐ fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm K) :
    ∃ (a : Kˣ) (b : ZMod n),
      gmPoint K a ≫ Sigma.ι (fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm K) b = x := by
  let Y := fun _ : ZMod n ↦ MultiplicativeGroupScheme.gm K
  let cover := FCurve.overSigmaCover Y
  let z : Spec (.of K) := Classical.choice inferInstance
  obtain ⟨b, y, hy⟩ := cover.exists_eq (x.left z)
  let i := (Sigma.ι Y b).left
  let : IsOpenImmersion i := inferInstanceAs (IsOpenImmersion (cover.f b))
  have hr : Set.range x.left ⊆ Set.range i := by
    rintro _ ⟨t, rfl⟩
    exact ⟨y, hy.trans (congrArg x.left (Subsingleton.elim z t))⟩
  let l := IsOpenImmersion.lift i x.left hr
  have hl : l ≫ i = x.left := IsOpenImmersion.lift_fac _ _ _
  let t : 𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K :=
    Over.homMk l (by
      rw [← (Sigma.ι Y b).w, ← Category.assoc, hl]
      exact x.w)
  obtain ⟨a, ha⟩ := gmPoint_surjective K t
  refine ⟨a, b, ?_⟩
  apply Over.OverMorphism.ext
  change (gmPoint K a).left ≫ i = x.left
  rw [ha]
  exact hl

end FLT.Mazur.PolygonGroupPoints

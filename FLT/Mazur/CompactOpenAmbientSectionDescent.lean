/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompactOpenSectionDescent
public import FLT.Mazur.OpenSectionTopComparison

/-!
# Descent of coordinates in ambient section rings

Translate the compact-open coordinate construction from global sections of open
subschemes to ambient sections, retaining the actual section pullback maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Ambient coordinates descend with restrictions and fixed transition coefficients. -/
theorem exists_compactOpen_ambient_sections {J : Type v} [SmallCategory J] [FinCategory J]
    (i : I) (O : J → (D.obj i).Opens)
    (hO : ∀ {j k}, (j ⟶ k) → O k ≤ O j)
    (hcompact : ∀ j, IsCompact (O j : Set (D.obj i)))
    (K L : J → Type v) [∀ j, Finite (K j)] [∀ j, Finite (L j)]
    (x : ∀ j, K j → Γ(c.pt, c.π.app i ⁻¹ᵁ O j))
    (τ : ∀ {j k}, (j ⟶ k) → K j → K k)
    (hx : ∀ {j k} (f : j ⟶ k) a,
      c.pt.presheaf.map (homOfLE ((c.π.app i).preimage_mono (hO f))).op (x j a) =
        (x k (τ f a) : Γ(c.pt, c.π.app i ⁻¹ᵁ O k)))
    (a b : ∀ j, L j → K j) (u : ∀ j, L j → Γ(D.obj i, O j))
    (hu : ∀ j l, x j (a j l) =
      @HMul.hMul Γ(c.pt, c.π.app i ⁻¹ᵁ O j) _ _ inferInstance
        ((c.π.app i).app (O j) (u j l)) (x j (b j l))) :
    ∃ (r : Over i) (y : ∀ j, K j → Γ(D.obj r.left, D.map r.hom ⁻¹ᵁ O j)),
      (∀ j k, ((c.π.app r.left).appLE _ _
        (by rw [← Scheme.Hom.comp_preimage, c.w])) (y j k) = x j k) ∧
      (∀ {j k} (f : j ⟶ k) l,
        (D.obj r.left).presheaf.map
          (homOfLE ((D.map r.hom).preimage_mono (hO f))).op (y j l) =
            (y k (τ f l) : Γ(D.obj r.left, D.map r.hom ⁻¹ᵁ O k))) ∧
      ∀ j l, y j (a j l) = (D.map r.hom).app (O j) (u j l) * y j (b j l) := by
  let x' j k := (c.π.app i ⁻¹ᵁ O j).topIso.inv (x j k)
  have hx' {j k} (f : j ⟶ k) l :
      (c.pt.homOfLE ((c.π.app i).preimage_mono (hO f))).appTop (x' j l) =
        (x' k (τ f l) : Γ((c.π.app i ⁻¹ᵁ O k).toScheme, ⊤)) := by
    change (c.pt.homOfLE _).appTop ((c.π.app i ⁻¹ᵁ O j).topIso.inv (x j l)) = _
    exact (topIso_inv_restriction (X := c.pt)
      ((c.π.app i).preimage_mono (hO f)) (x j l)).trans
        (congrArg (c.π.app i ⁻¹ᵁ O k).topIso.inv (hx f l))
  let u' j l := (O j).topIso.inv (u j l)
  have hu' j l : x' j (a j l) =
      (c.π.app i ∣_ O j).appTop (u' j l) * x' j (b j l) := by
    apply (ConcreteCategory.bijective_of_isIso (c.π.app i ⁻¹ᵁ O j).topIso.hom).injective
    simp only [map_mul, x', Iso.inv_hom_id_apply]
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, ← topIso_hom_resLE]
    simpa only [u', Iso.inv_hom_id_apply, Scheme.Hom.app_eq_appLE] using hu j l
  obtain ⟨r, z, hz, hnat, huz⟩ := exists_compactOpen_sections D c hc i O hO hcompact
    K L x' τ hx' a b u' hu'
  let y j k := (D.map r.hom ⁻¹ᵁ O j).topIso.hom (z j k)
  refine ⟨r, y, ?_, ?_, ?_⟩
  · intro j k
    change (c.π.app r.left).appLE _ _ _
      ((D.map r.hom ⁻¹ᵁ O j).topIso.hom (z j k)) = (x j k : Γ(c.pt, c.π.app i ⁻¹ᵁ O j))
    rw [topIso_hom_resLE]
    have he := hz j k
    change ((opensCone D c i (O j)).π.app r).appTop (z j k) =
      (c.π.app i ⁻¹ᵁ O j).topIso.inv (x j k) at he
    change (c.π.app i ⁻¹ᵁ O j).topIso.hom
      (((opensCone D c i (O j)).π.app r).appTop (z j k)) = _
    rw [he]
    exact congrArg (fun q : Γ(c.pt, c.π.app i ⁻¹ᵁ O j) ⟶ Γ(c.pt, c.π.app i ⁻¹ᵁ O j) ↦ q (x j k))
      (c.π.app i ⁻¹ᵁ O j).topIso.inv_hom_id
  · intro j k f l
    change (D.obj r.left).presheaf.map _
      ((D.map r.hom ⁻¹ᵁ O j).topIso.hom (z j l)) = _
    rw [topIso_hom_restriction, hnat]
  · intro j l
    change (D.map r.hom ⁻¹ᵁ O j).topIso.hom (z j (a j l)) = _
    rw [huz, map_mul, ← Scheme.Hom.resLE_eq_morphismRestrict, ← topIso_hom_resLE]
    simp only [u', Iso.inv_hom_id_apply, y, Scheme.Hom.app_eq_appLE]

end FLT.Mazur.Approximation

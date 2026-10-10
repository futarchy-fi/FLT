/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredDiagramUnitDescent
public import FLT.Mazur.OpenSectionFilteredColimit

/-!
# Descending units on finitely many compact opens

For affine inverse transitions between quasi-separated schemes, genuine units
on the inverse images of finitely many compact opens descend simultaneously.
The descended units retain their restriction and multiplication equations.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Natural units and finite multiplication laws descend on a fixed finite family of opens. -/
theorem exists_compactOpen_units {J : Type v} [SmallCategory J] [FinCategory J]
    (i : I) (O : J → (D.obj i).Opens)
    (hO : ∀ {j k}, (j ⟶ k) → O k ≤ O j)
    (hcompact : ∀ j, IsCompact (O j : Set (D.obj i)))
    (K L : J → Type v) [∀ j, Finite (K j)] [∀ j, Finite (L j)]
    (x : ∀ j, K j → Γ((c.π.app i ⁻¹ᵁ O j).toScheme, ⊤)ˣ)
    (τ : ∀ {j k}, (j ⟶ k) → K j → K k)
    (hx : ∀ {j k} (f : j ⟶ k) a,
      (c.pt.homOfLE ((c.π.app i).preimage_mono (hO f))).appTop (x j a) =
        (x k (τ f a) : Γ((c.π.app i ⁻¹ᵁ O k).toScheme, ⊤)))
    (a b d : ∀ j, L j → K j)
    (hmul : ∀ j l, x j (a j l) * x j (b j l) = x j (d j l)) :
    ∃ (r : Over i) (y : ∀ j, K j → Γ((D.map r.hom ⁻¹ᵁ O j).toScheme, ⊤)ˣ),
      (∀ j k, Units.map ((opensCone D c i (O j)).π.app r).appTop.hom.toMonoidHom
        (y j k) = x j k) ∧
      (∀ {j k} (f : j ⟶ k) l,
        ((D.obj r.left).homOfLE ((D.map r.hom).preimage_mono (hO f))).appTop (y j l) =
          (y k (τ f l) : Γ((D.map r.hom ⁻¹ᵁ O k).toScheme, ⊤))) ∧
      ∀ j l, y j (a j l) * y j (b j l) = y j (d j l) := by
  let F (j : J) := openSectionSystem D i (O j)
  let C (j : J) := openSectionCocone D c i (O j)
  let φ {j k : J} (f : j ⟶ k) : F j ⟶ F k := openSectionRestriction D i (hO f)
  let ψ {j k : J} (f : j ⟶ k) : (C j).pt ⟶ (C k).pt :=
    (c.pt.homOfLE ((c.π.app i).preimage_mono (hO f))).appTop
  obtain ⟨s, _, y, hy, hnat, hmul'⟩ := exists_filtered_diagram_units F C
    (fun j ↦ openSectionIsColimit D c i hc (O j) (hcompact j))
    φ ψ (fun f j ↦ openSectionCocone_restriction D c i (hO f) j)
    K L x τ hx a b d hmul (.op (Over.mk (𝟙 i)))
  exact ⟨s.unop, y, hy, hnat, hmul'⟩

end FLT.Mazur.Approximation

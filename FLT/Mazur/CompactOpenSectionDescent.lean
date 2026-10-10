/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredDiagramSectionDescent
public import FLT.Mazur.OpenSectionFilteredColimit
public import FLT.Mazur.OpenRestrictionLimitMap

/-!
# Descending section coordinates on finitely many compact opens

For affine inverse transitions between quasi-separated schemes, section coordinates
on the inverse images of finitely many compact opens descend simultaneously.
The descended coordinates retain restrictions and fixed transition equations.
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
/-- Coordinates descend with restrictions and equations from prescribed transition coefficients. -/
theorem exists_compactOpen_sections {J : Type v} [SmallCategory J] [FinCategory J]
    (i : I) (O : J → (D.obj i).Opens)
    (hO : ∀ {j k}, (j ⟶ k) → O k ≤ O j)
    (hcompact : ∀ j, IsCompact (O j : Set (D.obj i)))
    (K L : J → Type v) [∀ j, Finite (K j)] [∀ j, Finite (L j)]
    (x : ∀ j, K j → Γ((c.π.app i ⁻¹ᵁ O j).toScheme, ⊤))
    (τ : ∀ {j k}, (j ⟶ k) → K j → K k)
    (hx : ∀ {j k} (f : j ⟶ k) a,
      (c.pt.homOfLE ((c.π.app i).preimage_mono (hO f))).appTop (x j a) =
        (x k (τ f a) : Γ((c.π.app i ⁻¹ᵁ O k).toScheme, ⊤)))
    (a b : ∀ j, L j → K j)
    (u : ∀ j, L j → Γ((O j).toScheme, ⊤))
    (hu : ∀ j l, x j (a j l) =
      (c.π.app i ∣_ O j).appTop (u j l) * x j (b j l)) :
    ∃ (r : Over i) (y : ∀ j, K j → Γ((D.map r.hom ⁻¹ᵁ O j).toScheme, ⊤)),
      (∀ j k, ((opensCone D c i (O j)).π.app r).appTop
        (y j k) = x j k) ∧
      (∀ {j k} (f : j ⟶ k) l,
        ((D.obj r.left).homOfLE ((D.map r.hom).preimage_mono (hO f))).appTop (y j l) =
          (y k (τ f l) : Γ((D.map r.hom ⁻¹ᵁ O k).toScheme, ⊤))) ∧
      ∀ j l, y j (a j l) =
        (D.map r.hom ∣_ O j).appTop (u j l) * y j (b j l) := by
  let F (j : J) := openSectionSystem D i (O j)
  let C (j : J) := openSectionCocone D c i (O j)
  let φ {j k : J} (f : j ⟶ k) : F j ⟶ F k := openSectionRestriction D i (hO f)
  let ψ {j k : J} (f : j ⟶ k) : (C j).pt ⟶ (C k).pt :=
    (c.pt.homOfLE ((c.π.app i).preimage_mono (hO f))).appTop
  let e : Over i := Over.mk (𝟙 i)
  let u' j l := ((opensDiagramToOpen D i (O j)).app e).appTop (u j l)
  have hu' j l : x j (a j l) =
      @HMul.hMul Γ((c.π.app i ⁻¹ᵁ O j).toScheme, ⊤) _ _ inferInstance
        (((opensCone D c i (O j)).π.app e).appTop (u' j l)) (x j (b j l)) := by
    rw [hu]
    congr 1
    exact congrArg (fun f ↦ f.appTop (u j l)) (opensCone_toOpen D i (O j) c e).symm
  obtain ⟨s, h, y, hy, hnat, hu''⟩ := exists_filtered_diagram_sections F C
    (fun j ↦ openSectionIsColimit D c i hc (O j) (hcompact j))
    φ ψ (fun f j ↦ openSectionCocone_restriction D c i (hO f) j)
    K L x τ hx (.op e) a b u' hu'
  refine ⟨s.unop, y, hy, hnat, fun j l ↦ (hu'' j l).trans ?_⟩
  congr 1
  have he := (opensDiagramToOpen D i (O j)).naturality h.unop
  exact congrArg (fun f ↦ f.appTop (u j l)) (he.trans (Category.comp_id _))

end FLT.Mazur.Approximation

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalLocalCartierCubicUnrestricted
public import FLT.Mazur.CompatibleSubgroupGeneratorBaseChange

/-!
# Local original cubics with a prescribed Cartier generator

For a globally specified generator, choose the local cubic generator by the
full compatible comparison. The resulting section is identified with the
original pullback, rather than an unrelated local choice of generator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

include hP in
/-- Local pointed cubics retain the specified original Cartier generator. -/
theorem exists_prescribed_local_cartierCubic {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ (T : Scheme) (_ : IsAffine T) (f : T ⟶ S),
      Flat f ∧ LocallyOfFinitePresentation f ∧ x ∈ Set.range f ∧ Set.range f ⊆ V ∧
        ∃ (W : WeierstrassCurve Γ(T, ⊤)) (_ : W.IsElliptic)
          (J : (pointedCubicFamily W).FiniteSubgroup n) (Q : 𝟙_ (Over T) ⟶ J.carrier),
          J.IsCartierGenerator Q ∧ ∃ a : CompatibleIso J (H.baseChange f),
            Q ≫ a.subgroup.hom = pullSection f P := by
  obtain ⟨T, hT, f, hf, hl, hxf, hV, W, hW, J, _, _, ⟨a⟩⟩ :=
    (hP.isCyclic H).exists_original_local_cartierCubic_unrestricted H hx
  refine ⟨T, hT, f, hf, hl, hxf, hV, W, hW, J,
    pullSection f P ≫ a.subgroup.inv, a.symm.cartierGenerator (hP.baseChange H f), a, ?_⟩
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

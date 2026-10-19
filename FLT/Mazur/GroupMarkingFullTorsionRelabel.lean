/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FullTorsionMarkingRelabel
public import FLT.Mazur.GroupMarkingTransport

/-!
# Full torsion relabeling on actual group objects

Postcomposition by a group-object isomorphism gives an isomorphism on sections.
Two full faithful torsion markings therefore determine a unique label change.
-/

@[expose] public noncomputable section
open CategoryTheory MonObj
namespace FLT.Mazur.GroupMarkingTransport
universe u v w
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C] {L : Type w} [Group L]
  (G H : CommGrp C) (e : G ≅ H) (T : C)

/-- Postcomposition by the actual isomorphism, as an equivalence of section groups. -/
def sectionMulEquiv : (T ⟶ G.X) ≃* (T ⟶ H.X) where
  toFun s := s ≫ e.hom.hom.hom.hom
  invFun s := s ≫ e.inv.hom.hom.hom
  left_inv s := by
    change (s ≫ e.hom.hom.hom.hom) ≫ e.inv.hom.hom.hom = s
    have h := congrArg (fun f ↦ f.hom.hom.hom) e.hom_inv_id
    change e.hom.hom.hom.hom ≫ e.inv.hom.hom.hom = 𝟙 _ at h
    rw [Category.assoc, h, Category.comp_id]
  right_inv s := by
    change (s ≫ e.inv.hom.hom.hom) ≫ e.hom.hom.hom.hom = s
    have h := congrArg (fun f ↦ f.hom.hom.hom) e.inv_hom_id
    change e.inv.hom.hom.hom ≫ e.hom.hom.hom.hom = 𝟙 _ at h
    rw [Category.assoc, h, Category.comp_id]
  map_mul' s t := (IsMonHom.monoidHom e.hom.hom.hom.hom T).map_mul s t

/-- Two actual full torsion markings are compared by one unique label automorphism. -/
theorem existsUnique_full_torsion_relabel (n : ℕ)
    (m : L →* (T ⟶ G.X)) (v : L →* (T ⟶ H.X))
    (hm : Function.Injective m) (hv : Function.Injective v)
    (hmp : ∀ a, m a ^ n = 1) (hvp : ∀ a, v a ^ n = 1)
    (hmf : ∀ x, x ^ n = 1 → ∃ a, m a = x)
    (hvf : ∀ x, x ^ n = 1 → ∃ a, v a = x) :
    ∃! r : MulAut L, ∀ a, m (r a) ≫ e.hom.hom.hom.hom = v a :=
  FullTorsionMarking.existsUnique_relabel n m v hm hv hmp hvp hmf hvf
    (sectionMulEquiv G H e T)

end FLT.Mazur.GroupMarkingTransport

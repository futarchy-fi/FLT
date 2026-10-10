/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImmersionSections

/-!
# Global sections of an open chart

Reindex image-of-top sections to the actual open range. The resulting
isomorphism retains naturality, the counit and the pullback unit.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafOpenImmersionSections

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]

/-- Sections on the actual open range are global sections of the pullback. -/
def topSectionsIso (M : X.Modules) :
    Γ(M, i.opensRange) ≅ Γ((pullback i).obj M, ⊤) :=
  M.presheaf.mapIso (eqToIso i.image_top_eq_opensRange).op ≪≫ imageSectionsIso i M ⊤

/-- The range section comparison commutes with module morphisms. -/
lemma topSectionsIso_naturality {M N : X.Modules} (a : M ⟶ N) :
    a.app i.opensRange ≫ (topSectionsIso i N).hom =
      (topSectionsIso i M).hom ≫ ((pullback i).map a).app ⊤ := by
  unfold topSectionsIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  have hn := a.mapPresheaf.naturality (eqToHom i.image_top_eq_opensRange).op
  change M.presheaf.map _ ≫ a.app _ = a.app _ ≫ N.presheaf.map _ at hn
  rw [← Category.assoc, ← hn, Category.assoc, imageSectionsIso_naturality, Category.assoc]

/-- The chart counit is the canonical equality reindexing of sections on the range. -/
lemma topSectionsIso_counit (M : Y.Modules) :
    (topSectionsIso i ((pushforward i).obj M)).hom ≫
        (ModuleSheafOverlapImageTransition.openCounitIso i M).hom.app ⊤ =
      M.presheaf.map (eqToHom (Scheme.Hom.preimage_opensRange i).symm).op := by
  unfold topSectionsIso
  rw [Iso.trans_hom, Category.assoc, imageSectionsIso_counit]
  change M.presheaf.map _ ≫ M.presheaf.map _ = _
  rw [← Functor.map_comp]
  congr 1

/-- The range section isomorphism is the actual pullback unit, reindexed to top. -/
lemma topSectionsIso_unit (M : X.Modules) :
    (topSectionsIso i M).hom = ((pullbackPushforwardAdjunction i).unit.app M).app
        i.opensRange ≫ ((pullback i).obj M).presheaf.map
          (eqToHom (Scheme.Hom.preimage_opensRange i).symm).op := by
  rw [← imageSectionsIso_unit]
  rw [Category.assoc, ← imageSectionsIso_restrict]
  unfold topSectionsIso
  rw [← Category.assoc]
  change M.presheaf.map _ ≫ _ = (M.presheaf.map _ ≫ M.presheaf.map _) ≫ _
  rw [← Functor.map_comp]
  congr 2

end FLT.Mazur.ModuleSheafOpenImmersionSections

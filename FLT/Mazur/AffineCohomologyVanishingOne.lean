/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingCovers
public import FLT.Mazur.AffineCohomologyVanishingDescent

/-!
# First sheaf cohomology vanishes for affine tilde modules

Local surjectivity supplies lifts on a finite principal cover. The localization
Cech computation corrects and glues them. Applied to the quotient by an
injective embedding, this proves vanishing of the actual Ext-based `Sheaf.H`
in degree one. No acyclicity of cover intersections is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace FLT.Mazur.AffineCohomologyVanishingOne

open AffineCohomologyVanishingCovers AffineCohomologyVanishingDescent CechSheafHZero

variable {R : CommRingCat.{u}}

/-- Principal-cover first Cech exactness makes quotient sections lift globally. -/
lemma sections_surjective
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))}
    (hS : S.ShortExact)
    (hC : ∀ s : Finset R, Ideal.span (Set.range fun f : s ↦ (f : R)) = ⊤ →
      (C (fun f : s ↦ PrimeSpectrum.basicOpen (f : R)) S.X₁).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  classical
  have := hS.epi_g
  intro a
  have hg : TopCat.Presheaf.IsLocallySurjective S.g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr inferInstance
  let P (V : Opens (PrimeSpectrum R)) : Prop :=
    ∃ t, S.g.hom.app (op V) t = S.X₃.obj.map (homOfLE le_top).op a
  obtain ⟨s, hs, hlift⟩ := exists_finite_principal_cover ⊤
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set (PrimeSpectrum R)))) P
    (by
      rintro V V' hVV' ⟨t, ht⟩
      refine ⟨S.X₂.obj.map (homOfLE hVV').op t, ?_⟩
      rw [NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
    (by
      intro x _
      obtain ⟨V, hV, ht, hxV⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hg ⊤ a x trivial
      exact ⟨V, hxV, hV, ht⟩)
  have hlocal : ∀ f : s, ∃ t, S.g.hom.app (op (PrimeSpectrum.basicOpen (f : R))) t =
      S.X₃.obj.map (homOfLE le_top).op a := fun f ↦ hlift f.val f.property
  choose t ht using hlocal
  exact exists_section_lift _ hS hs (hC s (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hs))
    a t ht

variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology (TopCat.of (Spec R))) AddCommGrpCat.{u})]

/-- The cofinal principal-cover criterion in Ext degree one. -/
lemma sheafH_one_subsingleton
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R)))
    (hC : ∀ s : Finset R, Ideal.span (Set.range fun f : s ↦ (f : R)) = ⊤ →
      (C (fun f : s ↦ PrimeSpectrum.basicOpen (f : R)) F).ExactAt 1) :
    Subsingleton (Sheaf.H F 1) := by
  let S := CechAcyclicComparison.embeddingSequence F
  have hS := CechAcyclicComparison.embeddingSequence_shortExact F
  have hsurj := sections_surjective hS hC
  have hzero : Function.Surjective (Sheaf.H.map S.g 0) := by
    intro b
    obtain ⟨t, ht⟩ := hsurj (Sheaf.H.equiv₀ S.X₃ isTerminalTop b)
    refine ⟨(Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm t, ?_⟩
    apply (Sheaf.H.equiv₀ S.X₃ isTerminalTop).injective
    rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply, ht]
  apply subsingleton_of_forall_eq 0
  intro a
  obtain ⟨b, rfl⟩ := CechDimensionShift.sheafDelta_surjective hS 0 a
  exact ((ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' hS 0 1 rfl) b).mpr (hzero b)

/-- First Ext-based sheaf cohomology vanishes for every affine tilde module. -/
theorem tilde_sheafH_one_subsingleton (M : ModuleCat.{u} R) :
    Subsingleton (Sheaf.H (FCurve.moduleAbelianSheaf (tilde M)) 1) :=
  sheafH_one_subsingleton _ fun s hs ↦ principal_cech_exactAt (fun f : s ↦ (f : R)) M hs 0

/-- First Ext cohomology vanishes for every quasi-coherent sheaf on a spectrum. -/
theorem quasicoherent_sheafH_one_subsingleton (M : (Spec R).Modules)
    [M.IsQuasicoherent] : Subsingleton (Sheaf.H (FCurve.moduleAbelianSheaf M) 1) := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let f : FCurve.moduleAbelianSheaf (tilde (moduleSpecΓFunctor.obj M)) ⟶
      FCurve.moduleAbelianSheaf M :=
    (SheafOfModules.toSheaf (Spec R).ringCatSheaf).map M.fromTildeΓ
  have : IsIso f := Functor.map_isIso _ _
  have := tilde_sheafH_one_subsingleton (moduleSpecΓFunctor.obj M)
  have hinj : Function.Injective (Sheaf.H.map (inv f) 1) := by
    intro a b h
    have he := congrArg (Sheaf.H.map f 1) h
    simpa only [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply] using he
  exact hinj.subsingleton

end FLT.Mazur.AffineCohomologyVanishingOne

namespace FLT.Mazur.FCurve

local instance affineOneHasExt (R : CommRingCat.{u}) :
    HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (TopCat.of (Spec R))) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Vanishing in degree one for the module cohomology used by FC08. -/
theorem tilde_moduleH_one_subsingleton {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    Subsingleton (ModuleH (tilde M) 1) :=
  AffineCohomologyVanishingOne.tilde_sheafH_one_subsingleton M

/-- Quasi-coherent module cohomology on a spectrum vanishes in degree one. -/
theorem quasicoherent_moduleH_one_subsingleton {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] : Subsingleton (ModuleH M 1) :=
  AffineCohomologyVanishingOne.quasicoherent_sheafH_one_subsingleton M

end FLT.Mazur.FCurve

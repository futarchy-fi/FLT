/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVariableChangeGroup
public import FLT.EllipticCurve.CubicTorsionGroup
/-! # Functoriality of the represented cubic torsion scheme

Every group-scheme homomorphism restricts to the actual multiplication kernel.
The restriction respects composition and identity and is again a group
homomorphism. Pointed coordinate changes give isomorphisms of these kernels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
variable {V W U : WeierstrassCurve R} [V.IsElliptic] [W.IsElliptic] [U.IsElliptic]

theorem torsionInclusion_pow (V : WeierstrassCurve R) [V.IsElliptic] (n : ℕ) :
    (torsionInclusion V n) ^ n = 1 := by
  have h := (torsionModelPointEquiv V n (torsionModel V n) (𝟙 _)).property
  change (𝟙 _ ≫ torsionInclusion V n) ^ n = 1 at h
  simpa only [Category.id_comp] using h

/-- Restriction of a homomorphism of cubic group schemes to its n-torsion. -/
def torsionTransport (f : groupModel V ⟶ groupModel W) [IsMonHom f] (n : ℕ) :
    torsionModel V n ⟶ torsionModel W n :=
  (torsionModelPointEquiv W n (torsionModel V n)).symm
    ⟨torsionInclusion V n ≫ f, by
      rw [← MonObj.pow_comp, torsionInclusion_pow, MonObj.one_comp]⟩

@[reassoc (attr := simp)] theorem torsionTransport_inclusion
    (f : groupModel V ⟶ groupModel W) [IsMonHom f] (n : ℕ) :
    torsionTransport f n ≫ torsionInclusion W n = torsionInclusion V n ≫ f :=
  congrArg Subtype.val ((torsionModelPointEquiv W n (torsionModel V n)).apply_symm_apply _)

@[simp] theorem torsionTransport_id (V : WeierstrassCurve R) [V.IsElliptic] (n : ℕ) :
    torsionTransport (𝟙 (groupModel V)) n = 𝟙 _ := by
  apply (cancel_mono (torsionInclusion V n)).mp
  simp

theorem torsionTransport_comp (f : groupModel V ⟶ groupModel W) [IsMonHom f]
    (g : groupModel W ⟶ groupModel U) [IsMonHom g] (n : ℕ) :
    torsionTransport f n ≫ torsionTransport g n = torsionTransport (f ≫ g) n := by
  apply (cancel_mono (torsionInclusion U n)).mp
  simp only [Category.assoc, torsionTransport_inclusion, torsionTransport_inclusion_assoc]

instance torsionTransportIsMonHom (f : groupModel V ⟶ groupModel W) [IsMonHom f] (n : ℕ) :
    IsMonHom (torsionTransport f n) where
  one_hom := by
    apply (cancel_mono (torsionInclusion W n)).mp
    simp only [Category.assoc, torsionTransport_inclusion, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono (torsionInclusion W n)).mp
    simp only [Category.assoc, torsionTransport_inclusion, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, torsionTransport_inclusion]

theorem torsionTransport_congr {f g : groupModel V ⟶ groupModel W}
    [IsMonHom f] [IsMonHom g] (h : f = g) (n : ℕ) :
    torsionTransport f n = torsionTransport g n := by
  cases h
  rfl

/-- Isomorphisms of cubic group schemes induce isomorphisms of their full torsion schemes. -/
def torsionTransportIso (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] (n : ℕ) :
    torsionModel V n ≅ torsionModel W n where
  hom := torsionTransport e.hom n
  inv := torsionTransport e.inv n
  hom_inv_id :=
    (torsionTransport_comp e.hom e.inv n).trans
      ((torsionTransport_congr e.hom_inv_id n).trans (torsionTransport_id V n))
  inv_hom_id :=
    (torsionTransport_comp e.inv e.hom n).trans
      ((torsionTransport_congr e.inv_hom_id n).trans (torsionTransport_id W n))


instance torsionTransportIsoIsMonHom (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] (n : ℕ) :
    IsMonHom (torsionTransportIso e n).hom :=
  inferInstanceAs (IsMonHom (torsionTransport e.hom n))

instance torsionTransportIsoInvIsMonHom (e : groupModel V ≅ groupModel W)
    [IsMonHom e.hom] [IsMonHom e.inv] (n : ℕ) :
    IsMonHom (torsionTransportIso e n).inv :=
  inferInstanceAs (IsMonHom (torsionTransport e.inv n))

/-- The actual torsion-scheme isomorphism induced by an admissible coordinate change. -/
def variableChangeTorsionIso (W : WeierstrassCurve R) [W.IsElliptic]
    (C : VariableChange R) (n : ℕ) : torsionModel (C • W) n ≅ torsionModel W n :=
  torsionTransportIso (V := C • W) (W := W) (variableChangeOverIso W C) n


instance variableChangeTorsionIsoIsMonHom (W : WeierstrassCurve R) [W.IsElliptic]
    (C : VariableChange R) (n : ℕ) : IsMonHom (variableChangeTorsionIso W C n).hom := by
  change IsMonHom (torsionTransportIso (V := C • W) (W := W) (variableChangeOverIso W C) n).hom
  infer_instance

instance variableChangeTorsionIsoInvIsMonHom (W : WeierstrassCurve R) [W.IsElliptic]
    (C : VariableChange R) (n : ℕ) : IsMonHom (variableChangeTorsionIso W C n).inv := by
  change IsMonHom (torsionTransportIso (V := C • W) (W := W) (variableChangeOverIso W C) n).inv
  infer_instance

end WeierstrassCurve.CubicCharts


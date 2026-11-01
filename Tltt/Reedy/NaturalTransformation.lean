import Tltt.Reedy.ReedyPresheaf
import Tltt.Fibrancy.Cofibrancy

-- Object-universe wrappers require conversion through semireducible definitions.
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Tltt.ReedyFibrancy
open CategoryTheory

universe u v
variable {D : Type u} [DirectCategory.{u, max u v} D] {n : Nat}

/-- A transformation on the lower ranks, extended by compatible maps at the next rank. -/
@[ext]
structure NatTransExtension (A X : Psh (Below D (n+1))) where
  lower : NatTrans (restrict₁ A) (restrict₁ X)
  upper (i : OfRank D n) : A.obj (.op i.as_below) → X.obj (.op i.as_below)
  naturality {i : OfRank D n} {j : Below D n} (f : j.point ⟶ i.point)
    (a : A.obj (.op i.as_below)) :
    lower.app (.op j) (A.map (show j.up ⟶ i.as_below from f).op a) =
      X.map (show j.up ⟶ i.as_below from f).op (upper i a)

namespace NatTransExtension
section Reconstruction
variable {A X : Psh (Below D (n+1))}

def ofNatTrans (η : NatTrans A X) : NatTransExtension A X where
  lower := {
    app i := η.app (.op i.unop.up)
    naturality := by intro i j f; exact η.naturality ((Below.inclusion D n).op.map f)
  }
  upper i := η.app (.op i.as_below)
  naturality {i j} f a := by
    exact ConcreteCategory.congr_hom
      (η.naturality (show j.up ⟶ i.as_below from f).op) a

def toNatTrans (η : NatTransExtension A X) : NatTrans A X where
  app i :=
    if h : rk i.unop = n then
      ↾fun a => η.upper ⟨i.unop.point, h⟩ a
    else
      η.lower.app (.op (i.unop.of_succ_of_rk_ne h))
  naturality := by
    intro i j f
    apply ConcreteCategory.ext_apply
    intro a
    by_cases hi : rk i.unop = n
    · by_cases hj : rk j.unop = n
      · have e : j.unop = i.unop := by
          apply Below.ext
          exact eq_of_map_of_rk_eq_rk f.unop (hj.trans hi.symm)
        have eo : j = i := congrArg Opposite.op e
        subst j
        have hf : f = 𝟙 i := by
          apply Quiver.Hom.unop_inj
          apply eq_id
        subst f
        simp [hi, TypeCat.ofHom_apply]
      · simp only [hi, hj, dite_eq_left, types_comp_apply, TypeCat.ofHom_apply]
        change η.lower.app (.op (j.unop.of_succ_of_rk_ne hj)) (A.map f a) =
          X.map f (η.upper ⟨i.unop.point, hi⟩ a)
        exact η.naturality (i := ⟨i.unop.point, hi⟩)
          (j := j.unop.of_succ_of_rk_ne hj) f.unop a
    · have hj : rk j.unop ≠ n := by
        intro hj
        have hle := leq_of_map f.unop
        have hil := (i.unop.of_succ_of_rk_ne hi).rank_is_lt
        have hle' : n ≤ rk i.unop := by simpa only [hj] using hle
        exact Nat.not_lt_of_ge hle' hil
      simp only [hi, hj, types_comp_apply]
      change η.lower.app (.op (j.unop.of_succ_of_rk_ne hj)) (A.map f a) =
        X.map f (η.lower.app (.op (i.unop.of_succ_of_rk_ne hi)) a)
      exact ConcreteCategory.congr_hom
        (η.lower.naturality (show
          Opposite.op (i.unop.of_succ_of_rk_ne hi) ⟶
          Opposite.op (j.unop.of_succ_of_rk_ne hj) from f.unop.op)) a

theorem to_of (η : NatTrans A X) : toNatTrans (ofNatTrans η) = η := by
  apply NatTrans.ext
  funext i
  apply ConcreteCategory.ext_apply
  intro a
  by_cases h : rk i.unop = n
  · simp [toNatTrans, ofNatTrans, h]
    rfl
  · simp [toNatTrans, ofNatTrans, h]
    rfl

theorem of_to (η : NatTransExtension A X) : ofNatTrans (toNatTrans η) = η := by
  apply NatTransExtension.ext
  · apply NatTrans.ext
    funext i
    apply ConcreteCategory.ext_apply
    intro a
    have h : rk i.unop.up ≠ n := Nat.ne_of_lt i.unop.rank_is_lt
    simp [toNatTrans, ofNatTrans, h]
    rfl
  · funext i a
    have h : rk i.as_below = n := i.rank_is
    simp [toNatTrans, ofNatTrans, h]
    rfl

def equiv (A X : Psh (Below D (n+1))) : NatTrans A X ≃ NatTransExtension A X where
  toFun := ofNatTrans
  invFun := toNatTrans
  left_inv := to_of
  right_inv := of_to


end Reconstruction

def boundaryCone (i : D) (A X : Psh (Below D (rk i + 1)))
    (η : NatTrans (restrict₁ A) (restrict₁ X)) :
    Limits.Cone (MatchingObject.functor i (restrict₁ X)) where
  pt := A.obj (.op (Below.in_own_layer i))
  π := {
    app j := A.map (show ((under.inclusion D i).obj j.unop).up ⟶
      Below.in_own_layer i from j.unop.snd.val).op ≫
        η.app (.op ((under.inclusion D i).obj j.unop))
    naturality := by
      intro j k f
      change _ = (_ ≫ _) ≫ (restrict₁ X).map ((under.inclusion D i).op.map f)
      erw [Category.assoc, ← η.naturality]
      change A.map _ ≫ η.app _ = A.map _ ≫ (A.map _ ≫ η.app _)
      erw [← Category.assoc, ← A.map_comp]
      congr 2
      exact congrArg Quiver.Hom.op f.unop.property.symm
  }

def boundaryLift (i : D) (A X : Psh (Below D (rk i + 1)))
    (η : NatTrans (restrict₁ A) (restrict₁ X)) :
    A.obj (.op (Below.in_own_layer i)) → MatchingObject i (restrict₁ X) :=
  (MatchingObject.limit_cone i (restrict₁ X)).isLimit.lift (boundaryCone i A X η)

theorem boundaryLift_fac (i : D) (A X : Psh (Below D (rk i + 1)))
    (η : NatTrans (restrict₁ A) (restrict₁ X)) (j : (under i)ᵒᵖ)
    (a : A.obj (.op (Below.in_own_layer i))) :
    (MatchingObject.limit_cone i (restrict₁ X)).cone.π.app j (boundaryLift i A X η a) =
      (boundaryCone i A X η).π.app j a :=
  ConcreteCategory.congr_hom
    ((MatchingObject.limit_cone i (restrict₁ X)).isLimit.fac (boundaryCone i A X η) j) a

theorem canonical_fac (i : D) (X : Psh (Below D (rk i + 1))) (j : (under i)ᵒᵖ)
    (b : X.obj (.op (Below.in_own_layer i))) :
    (MatchingObject.limit_cone i (restrict₁ X)).cone.π.app j (MatchingObject.canonical i X b) =
      (MatchingObject.Canonical.canonical_cone i X).π.app j b :=
  ConcreteCategory.congr_hom
    ((MatchingObject.limit_cone i (restrict₁ X)).isLimit.fac
      (MatchingObject.Canonical.canonical_cone i X) j) b

theorem matching_ext (i : D) (X : Psh (Below D (rk i)))
    {a b : MatchingObject i X}
    (h : ∀ j, (MatchingObject.limit_cone i X).cone.π.app j a =
      (MatchingObject.limit_cone i X).cone.π.app j b) : a = b := by
  have e : (↾fun _ : PUnit => a) = (↾fun _ : PUnit => b) := by
    apply (MatchingObject.limit_cone i X).isLimit.hom_ext
    intro j
    apply ConcreteCategory.ext_apply
    intro _
    exact h j
  exact ConcreteCategory.congr_hom e PUnit.unit

theorem boundary_eq_iff (i : D) (A X : Psh (Below D (rk i + 1)))
    (η : NatTrans (restrict₁ A) (restrict₁ X))
    (a : A.obj (.op (Below.in_own_layer i))) (b : X.obj (.op (Below.in_own_layer i))) :
    MatchingObject.canonical i X b = boundaryLift i A X η a ↔
      ∀ (j : Below D (rk i)) (f : j.point ⟶ i),
        η.app (.op j) (A.map (show j.up ⟶ Below.in_own_layer i from f).op a) =
          X.map (show j.up ⟶ Below.in_own_layer i from f).op b := by
  constructor
  · intro e j f
    have ne : i ≠ j.point := by
      intro e
      exact (Nat.ne_of_lt j.rank_is_lt) (congrArg rk e.symm)
    let j' : (under i)ᵒᵖ := .op ⟨j.point, f, ne⟩
    have h := congrArg (fun z => (MatchingObject.limit_cone i (restrict₁ X)).cone.π.app j' z) e
    rw [canonical_fac, boundaryLift_fac] at h
    exact h.symm
  · intro h
    apply matching_ext
    intro j
    rw [canonical_fac, boundaryLift_fac]
    exact (h ((under.inclusion D i).obj j.unop) j.unop.snd.val).symm


def boundaryMapAt (i : OfRank D n) (X : Psh (Below D (n+1))) :
    X.obj (.op i.as_below) → MatchingObject i.point (restrict₅ i (restrict₁ X)) := by
  rcases i with ⟨i, h⟩
  cases h
  exact MatchingObject.canonical i X

def boundaryLiftAt (i : OfRank D n) (A X : Psh (Below D (n+1)))
    (η : NatTrans (restrict₁ A) (restrict₁ X)) :
    A.obj (.op i.as_below) → MatchingObject i.point (restrict₅ i (restrict₁ X)) := by
  rcases i with ⟨i, h⟩
  cases h
  exact boundaryLift i A X η

theorem boundary_eq_iff_at (i : OfRank D n) (A X : Psh (Below D (n+1)))
    (η : NatTrans (restrict₁ A) (restrict₁ X))
    (a : A.obj (.op i.as_below)) (b : X.obj (.op i.as_below)) :
    boundaryMapAt i X b = boundaryLiftAt i A X η a ↔
      ∀ (j : Below D n) (f : j.point ⟶ i.point),
        η.app (.op j) (A.map (show j.up ⟶ i.as_below from f).op a) =
          X.map (show j.up ⟶ i.as_below from f).op b := by
  rcases i with ⟨i, h⟩
  cases h
  exact boundary_eq_iff i A X η a b

abbrev BoundaryFiber (A X : Psh (Below D (n+1)))
    (η : NatTrans (restrict₁ A) (restrict₁ X)) (i : OfRank D n)
    (a : A.obj (.op i.as_below)) :=
  { b : X.obj (.op i.as_below) // boundaryMapAt i X b = boundaryLiftAt i A X η a }

def fiberEquiv (A X : Psh (Below D (n+1))) : NatTransExtension A X ≃
    Σ η : NatTrans (restrict₁ A) (restrict₁ X), ∀ i a, BoundaryFiber A X η i a where
  toFun ε := ⟨ε.lower, fun i a => ⟨ε.upper i a,
    (boundary_eq_iff_at i A X ε.lower a (ε.upper i a)).mpr (fun j f => ε.naturality f a)⟩⟩
  invFun ε := {
    lower := ε.1
    upper i a := (ε.2 i a).val
    naturality := by
      intro i j f a
      exact (boundary_eq_iff_at i A X ε.1 a (ε.2 i a).val).mp (ε.2 i a).property j f
  }
  left_inv ε := by rfl
  right_inv ε := by rfl

/-- Extending a transformation amounts to choosing elements of matching-map fibers. -/
def equivFibers (A X : Psh (Below D (n+1))) : NatTrans A X ≃
    Σ η : NatTrans (restrict₁ A) (restrict₁ X), ∀ i a, BoundaryFiber A X η i a :=
  (equiv A X).trans (fiberEquiv A X)

open _root_.Tltt.Fibrancy
@[instance_reducible]
def boundaryFiber_fibrant (A : Psh (Below D (n+1))) (X : ReedyPresheaf D (n+1))
    (η : NatTrans (restrict₁ A) (restrict₁ X.presheaf))
    (i : OfRank D n) (a : A.obj (.op i.as_below)) :
    IsFibrantWeak.{max u v, max u v} (BoundaryFiber A X.presheaf η i a) := by
  apply strict_fibration_fiber_fibrant
  rcases i with ⟨i, h⟩
  cases h
  exact X.is_reedy (Below.in_own_layer i)


def emptyNatTransEquiv (A X : Psh (Below D 0)) : NatTrans A X ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := {
    app i := False.elim i.unop.not_below_zero
    naturality := by intro i; exact False.elim i.unop.not_below_zero
  }
  left_inv η := by
    apply NatTrans.ext
    funext i
    exact False.elim i.unop.not_below_zero
  right_inv _ := rfl

/-- Product closure for ranks and source values makes each extension fibrant. -/
@[instance_reducible]
def nat_trans_fibrant_of_pi
    (cofibrant_ranks : ∀ k, IsPiFibrant.{u, max u v, max u v} (OfRank D k)) (X : ReedyPresheaf D n)
    (A : Psh (Below D n)) (cofibrant_values : ∀ i, IsPiFibrant.{max u v, max u v, max u v} (A.obj i)) :
    IsFibrantWeak.{max u v, max u v} (NatTrans A X.presheaf) := by
  induction n with
  | zero =>
    exact fibrant_of_eqv_fibrant unit_is_fibrant (emptyNatTransEquiv A X.presheaf).symm
  | succ n ih =>
    apply fibrant_of_eqv_fibrant (α_eqv_β := (equivFibers A X.presheaf).symm)
    apply sigma_fibrant.{max u v, max u v, max u v, max u v}
    · let lower : ReedyPresheaf D n := {
        presheaf := restrict₁ X.presheaf
        is_reedy := (LayeredReedyPresheaf.of_rd_psh X).is_reedy
      }
      exact ih lower (restrict₁ A) (fun i => cofibrant_values (.op i.unop.up))
    · intro η
      apply (cofibrant_ranks n).pi_fibrant
      intro i
      apply (cofibrant_values (.op i.as_below)).pi_fibrant
      intro a
      exact boundaryFiber_fibrant A X η i a

@[instance_reducible]
def nat_trans_fibrant_finite
    (finite_ranks : ∀ k, Finite (OfRank D k)) (X : ReedyPresheaf D n)
    (A : Psh (Below D n)) (finite_values : ∀ i, Finite (A.obj i)) :
    IsFibrantWeak.{max u v, max u v} (NatTrans A X.presheaf) :=
  nat_trans_fibrant_of_pi (fun k => @finite_pi_fibrant _ (finite_ranks k)) X A
    (fun i => @finite_pi_fibrant _ (finite_values i))

end NatTransExtension
end Tltt.ReedyFibrancy

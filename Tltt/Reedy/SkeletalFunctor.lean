import Mathlib.Tactic.TypeStar
import Tltt.DirectCategories
import Tltt.Reedy.NaturalTransformation
import Tltt.Fibrancy
import Misc

namespace Tltt.ReedyFibrancy
open CategoryTheory
open Fibrancy

variable {D : Type*} [DirectCategory D]

def Sk (n : Nat) (A : Psh D) : Psh D where
  obj d :=
    if rk d.unop < n then A.obj d else Empty

  map {j i} f := by
    refine ↾?_
    if h : rk j.unop < n then
      have rk_i_lt_n : rk i.unop < n := calc
        rk i.unop ≤ rk j.unop := leq_of_map f.unop
        rk j.unop < n := h
      have h₁ : (if rk j.unop < n then A.obj j else Empty) = A.obj j := ite_eq_left h
      have h₂ : (if rk i.unop < n then A.obj i else Empty) = A.obj i := ite_eq_left rk_i_lt_n
      exact eqToHom h₂.symm ∘ A.map f ∘ eqToHom h₁
    else
      have h₁ : (if rk j.unop < n then A.obj j else Empty) = Empty := ite_eq_right h
      refine ?map ∘ eqToHom h₁
      intro
      contradiction

  map_id := by
    intro j
    apply ConcreteCategory.ext_apply
    intro x
    by_cases h : rk j.unop < n
    · simp [h]
    · have h₁ : (if rk j.unop < n then A.obj j else Empty) = Empty := ite_eq_right h
      rw [h₁] at x
      contradiction

  map_comp := by
    intro j i k f g
    apply ConcreteCategory.ext_apply
    intro x
    by_cases h : rk j.unop < n
    · have hi : rk i.unop < n := lt_of_le_of_lt (leq_of_map f.unop) h
      simp only [h, hi, dite_eq_left, TypeCat.ofHom_apply, types_comp_apply,
        Function.comp_apply, Functor.map_comp]
      have cancel {α β : Type _} (p : α = β) (q : β = α) (y : α) :
          eqToHom (C := Type _) q (eqToHom (C := Type _) p y) = y := by
        cases p
        rfl
      erw [cancel]
    · have h₁ : (if rk j.unop < n then A.obj j else Empty) = Empty := ite_eq_right h
      rw [h₁] at x
      contradiction

universe u v in
noncomputable def nat_trans_fibrant {D : Type u} [DirectCategory.{u, max u v} D] {n : Nat}
    (X : ReedyPresheaf D n) (A : Psh (Below D n))
    (cofibrant_ranks : ∀ k, IsCofibrant.{u, max u v, max u v} (OfRank D k))
    (cofibrant_values : ∀ i, IsCofibrant.{max u v, max u v, max u v} (A.obj i)) :
    IsFibrantWeak.{max u v, max u v} (NatTrans A X.presheaf) :=
  NatTransExtension.nat_trans_fibrant_of_pi (fun k => (cofibrant_ranks k).toIsPiFibrant) X A
    (fun i => (cofibrant_values i).toIsPiFibrant)

end Tltt.ReedyFibrancy

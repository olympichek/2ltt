import Mathlib.Tactic.TypeStar
import Tltt.DirectCategories
import Tltt.Fibrancy
import Tltt.Reedy.ReedyPresheaf
import Tltt.Reedy.SkeletalFunctor
import Misc

noncomputable section
namespace Tltt.ReedyFibrancy
open CategoryTheory
open Limits (Cone IsLimit)
open Iso (toEquiv)
open Limits.Types (constPUnitFunctor)
open Limits.IsLimit (conePointUniqueUpToIso)
open Fibrancy

variable {J : Type*} [DirectCategory J]

def border (j : J) : Psh J where
  obj i := { f : i.unop ⟶ j // i.unop ≠ j }

  map := by
    intro ⟨l⟩ ⟨i⟩ f
    refine ↾?_
    intro ⟨g, l_neq_j⟩
    have f := f.unop
    dsimp only at f g l_neq_j ⊢
    exists f ≫ g
    intro i_eq_j
    apply Nat.lt_irrefl <| rank.obj i
    calc
      _ ≤ rank.obj l := by
        apply PLift.down
        apply ULift.down
        apply rank.map
        assumption
      _ < rank.obj j := by
        apply Nat.lt_of_le_of_ne
        · apply PLift.down
          apply ULift.down
          apply rank.map
          assumption
        · intro rk_l_eq_rk_j
          apply l_neq_j
          apply Eq.symm
          exact congrArg Sigma.fst <| DirectCategory.reflect_identity _ _ g rk_l_eq_rk_j
      _ = rank.obj i := by rw [i_eq_j]

  map_id := by
    intro ⟨i⟩
    dsimp only
    apply ConcreteCategory.ext_apply
    intro ⟨f, i_neq_j⟩
    simp

  map_comp := by
    intro ⟨i⟩ ⟨k⟩ ⟨l⟩ f g
    have f := f.unop
    have g := g.unop
    apply ConcreteCategory.ext_apply
    intro ⟨h, i_neq_j⟩
    dsimp only at f g h i_neq_j
    simp

macro " ∂" j:term : term => ``(border $j)

def border_inc_yoneda (j : J) : NatTrans (∂j) (𝐲j) where
  app := by
    intro ⟨i⟩
    refine ↾?_
    intro ⟨f, _⟩
    exact f
  naturality := by
    intro ⟨k⟩ ⟨l⟩ f
    have f := f.unop
    unfold border yoneda
    apply ConcreteCategory.ext_apply
    intro ⟨g, k_neq_j⟩
    dsimp only at f g k_neq_j
    simp

section
  variable (i : J) (X : Psh (Below J (rk i)))

  def MatchObj.cone : Cone (MatchingObject.functor i X) where
    pt := NatTrans (restrict₃ (∂i)) X
    π := {
      app := by
        intro ⟨_, f, i_neq⟩
        simp [under.inclusion]
        refine ↾?_
        intro η
        refine η.app _ ?_
        simp [restrict₃, border]
        exists f
        intro
        apply i_neq
        apply Eq.symm
        assumption
      naturality := by
        intro ⟨j, f, i_neq_j⟩ ⟨k, g, i_neq_k⟩ ⟨h, p⟩
        simp at h p ⊢
        apply ConcreteCategory.ext_apply
        intro η
        simp [under.inclusion]
        let j' : Below J (rk i) := .mk j <| by
          apply Nat.lt_of_le_of_ne
          · apply leq_of_map
            assumption
          · intro
            apply i_neq_j
            apply Eq.symm
            apply eq_of_map_of_rk_eq_rk <;> assumption
        let k' : Below J (rk i) := .mk k <| by
          apply Nat.lt_of_le_of_ne
          · apply leq_of_map
            assumption
          · intro
            apply i_neq_k
            apply Eq.symm
            apply eq_of_map_of_rk_eq_rk <;> assumption
        have := η.naturality (X := .op j') (Y := .op k') h.op
        dsimp [restrict₃, border, Below.forget] at this
        rw [← p]
        exact ConcreteCategory.congr_hom this ⟨f, _⟩
    }

  def MatchObj : Type _ :=
    MatchObj.cone i X |>.pt

  def MatchObj.cone_is_limit : IsLimit (cone i X) where
    lift ψ := ↾fun x => {
      app := by
        intro ⟨j⟩
        simp [restrict₃, border]
        refine ↾?_
        intro ⟨f, j_neq_i⟩
        have i_neq_j := Ne.symm j_neq_i
        have := ψ.π.app ⟨_, f, i_neq_j⟩ x
        simp [under.inclusion] at this
        exact this
      naturality := by
        intro ⟨j⟩ ⟨k⟩ ⟨f⟩
        simp [restrict₃, border, Below.forget] at f ⊢
        apply ConcreteCategory.ext_apply
        intro ⟨g, j_neq_i⟩
        have i_neq_j := Ne.symm j_neq_i
        let j' : under i := .mk j.point <| by
          exists g
        let k' : under i := .mk k.point <| by
          exists f ≫ g
          intro i_eq_k
          apply Nat.lt_irrefl (rk i)
          conv => lhs; rw [i_eq_k]
          apply k.rank_is_lt
        let f' : k' ⟶ j' := .mk f <| by
          rfl
        have := ψ.π.naturality (X := .op j') (Y := .op k') f'.op
        simp at this ⊢
        exact ConcreteCategory.congr_hom this x
    }
    fac ψ := by
      intro
      apply ConcreteCategory.ext_apply
      intro x
      rfl
    uniq ψ := by
      intro m e
      apply ConcreteCategory.ext_apply
      intro x
      simp
      apply NatTrans.ext
      funext ⟨j⟩
      apply ConcreteCategory.ext_apply
      intro g
      simp [restrict₃, border, Below.forget] at g
      let j' : under i := .mk j.point <| by
        exists g
        apply Ne.symm
        exact g.property
      have := e (.op j')
      simp [cone] at this
      apply ConcreteCategory.congr_hom this

  def match_obj_eqv (i : J) (F : Psh (Below J (rk i)))
                    : MatchObj i F ≃ MatchingObject i F := by
    -- Lemma 4.5 of the article "Two-level type theory and applications"
    apply toEquiv
    apply IsLimit.conePointUniqueUpToIso
    · apply MatchObj.cone_is_limit
    · apply MatchingObject.limit_cone _ _ |>.isLimit
end

def MatchObj.canonical (F : Psh J) (j : J) : F.obj (.op j) → MatchObj j (restrict₃ F) := by
  intro fj
  have yj_to_F : (𝐲j) ⟶ F := yonedaEquiv.symm fj
  have bj_to_yj : (∂j) ⟶ (𝐲j) := border_inc_yoneda j
  apply restrict₆
  exact bj_to_yj ≫ yj_to_F

section Fibrancy
  universe u v
  variable {J : Type u} [DirectCategory.{u, max u v} J]

section
  variable {n : Nat} (X : ReedyPresheaf J n)

  def limit_is_fibrant (C : Cone X.presheaf) (p : IsLimit C)
      (cofibrant_ranks : ∀ k, IsCofibrant.{u, max u v, max u v} (OfRank J k)) :
      IsFibrantWeak.{max u v, max u v} C.pt := by
    apply fibrant_of_eqv_fibrant (α := NatTrans (constPUnitFunctor _) X.presheaf)
    · apply nat_trans_fibrant _ _ cofibrant_ranks
      intro j
      change IsCofibrant PUnit
      letI : Finite PUnit := Finite.of_fintype _
      exact finite_is_cofibrant _
    · apply toEquiv
      apply conePointUniqueUpToIso (s := cone_of_nat_unit _)
      apply cone_of_nat_unit_is_lim
      assumption
end

section
  variable (i : J) (X : ReedyPresheaf J (rk i))

  def match_obj_fibrant
      (cofibrant_ranks : ∀ k, IsCofibrant.{u, max u v, max u v} (OfRank J k))
      (cofibrant_homs : ∀ j : J, IsCofibrant.{max u v, max u v, max u v} (j ⟶ i)) :
      IsFibrantWeak.{max u v, max u v} (MatchObj i X.presheaf) := by
    classical
    apply nat_trans_fibrant _ _ cofibrant_ranks
    intro j
    exact cofibrant_subtype_const (cofibrant_homs j.unop.point) (j.unop.point ≠ i)

  def matching_object_fibrant
      (cofibrant_ranks : ∀ k, IsCofibrant.{u, max u v, max u v} (OfRank J k))
      (cofibrant_homs : ∀ j : J, IsCofibrant.{max u v, max u v, max u v} (j ⟶ i)) :
      IsFibrantWeak.{max u v, max u v} (MatchingObject i X.presheaf) := by
    apply fibrant_of_eqv_fibrant (α := MatchObj i X.presheaf)
    · exact match_obj_fibrant i X cofibrant_ranks cofibrant_homs
    · apply match_obj_eqv
end
end Fibrancy

end Tltt.ReedyFibrancy
end

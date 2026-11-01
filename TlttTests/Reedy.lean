import Tltt

-- The Reedy construction must remain independent of admissions and inner univalence.
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in [``Tltt.ReedyFibrancy.LayeredReedyPresheaf.eqv_of_layer_below,
      ``Tltt.ReedyFibrancy.CompactLRP.compact_eqv_layered,
      ``Tltt.ReedyFibrancy.nat_trans_fibrant,
      ``Tltt.ReedyFibrancy.matching_object_fibrant,
      ``Tltt.Fibrancy.finite_is_cofibrant,
      ``Tltt.cofibrant_reedy_presheaf_is_fibrant,
      ``Tltt.finite_reedy_presheaf_is_fibrant, ``Tltt.SemiSimplicialType] do
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Reedy declaration {declaration} depends on unexpected axiom {axiomName}"

noncomputable section
namespace TlttTests
open CategoryTheory Tltt Tltt.Fibrancy Tltt.ReedyFibrancy

-- An infinite fibrant source is accepted without a finiteness witness.
private def naturalSource : Psh (Below SemiSimplexCat 1) :=
  (Functor.const (Below SemiSimplexCat 1)ᵒᵖ).obj (Hott.Natₒ : Type)

example (X : ReedyPresheaf SemiSimplexCat 1) :
    IsFibrantWeak (NatTrans naturalSource X.presheaf) := by
  apply nat_trans_fibrant X naturalSource
  · intro k
    letI := SemiSimplexCat.finite_rank k
    exact finite_is_cofibrant _
  · intro i
    change IsCofibrant Hott.Natₒ
    exact fibrant_is_cofibrant (fibrant_weakening (ι := lift_is_fibrant _))

end TlttTests

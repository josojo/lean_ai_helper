from src.trace.trace import TracedTacticState


def test_is_finishing_proof() -> None:
    traced_tactic = TracedTacticState(
        "case a\nα : Type u\nβ : Type v\nι : Sort w\nγ : Type x\ns t : \
        Set α\na : α\nhs : Set.Finite s\nht : Set.Finite t\ninst✝¹ : \
        Fintype α\np : α → Prop\ninst✝ : DecidablePred p\nh : Set.Finite \
        {x | p x}\na✝ : α\n⊢ a✝ ∈ Finite.toFinset h ↔ a✝ ∈ Finset.filter p Finset.univ",
        "no goals",
        5966,
        5993,
    )
    assert traced_tactic.is_tactic_finishing_proof()
    traced_tactic = TracedTacticState(
        "case a\nα : Type u\nβ : Type v\nι : Sort w\nγ : Type x\ns t : \
        Set α\na : α\nhs : Set.Finite s\nht : Set.Finite t\ninst✝¹ : \
        Fintype α\np : α → Prop\ninst✝ : DecidablePred p\nh : \
        Set.Finite {x | p x}\na✝ : α\n⊢ a✝ ∈ Finite.toFinset h ↔ a✝ ∈ Finset.filter p Finset.univ",
        "no gdoals",
        5966,
        5993,
    )
    assert not traced_tactic.is_tactic_finishing_proof()

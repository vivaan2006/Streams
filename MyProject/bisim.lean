inductive State
| s1
| s2

def R : State → State → Prop :=
   fun s₁ s₂ => s₁ = s₂ -- was plannign on using lambda but i think its removed

inductive Transition : State → State → Prop
| s1_to_s2 : Transition State.s1 State.s2
| s2_to_s1 : Transition State.s2 State.s1

def is_bisimulation (R : State → State → Prop) : Prop :=
  ∀ (s₁ s₂ : State),
    R s₁ s₂ →
    (∀ (s₁' : State),
      Transition s₁ s₁' →
      ∃ (s₂' : State),
        Transition s₂ s₂' ∧ R s₁' s₂') ∧
    ∀ (s₂' : State),
      Transition s₂ s₂' →
      ∃ (s₁' : State),
        Transition s₁ s₁' ∧ R s₁' s₂'

theorem bisimulation_proof : is_bisimulation R :=
begin
  intro s₁ s₂ h, -- intros or assume??--
  split,
  {
    intro s₁' h₁,
    cases h₁,
    { exact ⟨State.s2, Transition.s1_to_s2, rfl⟩ },
    { exact ⟨State.s1, Transition.s2_to_s1, rfl⟩ },
  },
  {
    intro s₂' h₂,
    cases h₂,
    { exact ⟨State.s1, Transition.s2_to_s1, rfl⟩ },
    { exact ⟨State.s2, Transition.s1_to_s2, rfl⟩ },
  }
end

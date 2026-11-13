module

public import EthLib.Consensus.Proofs.Transition.Chain

/-!
# Proofs: a chain of beacon states given as the list of its steps

A run of `ChainStep` is a proof, so it cannot give back the block that a block step applies.

A chain given as data keeps each of its steps, and the signed block of each block step.

Its steps, its states and the blocks it applies are then lists, in the order of the chain.

Each such chain is a run of `ChainStep`, so every theorem about runs applies to it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A chain of beacon states from a first state, given as its steps, the last step outermost.

A slot step is a slot with the upgrades due at the slot it reaches.

A block step is a signed block at the slot of the state, on the state of its fork.

It keeps the execution engine, the signed block and the flag of validation that it uses. -/
inductive ChainList (config : Config) (checks : SignatureChecks)
    (first : ForkedBeaconState preset) : ForkedBeaconState preset → Type
  /-- The chain with no step, at its first state. -/
  | nil : ChainList config checks first first
  /-- A chain, then a slot with the upgrades due at the slot it reaches. -/
  | slot {forked after : ForkedBeaconState preset} (earlier : ChainList config checks first forked)
    (computed : advanceSlotAcross config checks forked = .ok after) :
    ChainList config checks first after
  /-- A chain, then a signed block at the slot of its last state, on the state of its fork. -/
  | block {fork : Fork} {state after : BeaconState preset fork}
    (earlier : ChainList config checks first ⟨fork, state⟩) (engine : ExecutionEngine preset fork)
    (signed : SignedBeaconBlock preset fork) (validateResult : Bool)
    (applied : applySignedBlock config checks engine state signed validateResult = .ok after) :
    ChainList config checks first ⟨fork, after⟩

/-- A block that a chain applies, with the states before and after it. -/
structure AppliedBlock (preset : Preset) where
  /-- The fork of the two states and of the block. -/
  fork : Fork
  /-- The state before the block. -/
  before : BeaconState preset fork
  /-- The signed block. -/
  signed : SignedBeaconBlock preset fork
  /-- The state after the block. -/
  after : BeaconState preset fork

namespace ChainList

variable {first : ForkedBeaconState preset}

/-- The steps of a chain, each as the pair of the states before and after it, in order. -/
def steps : {last : ForkedBeaconState preset} → ChainList config checks first last →
    List (ForkedBeaconState preset × ForkedBeaconState preset)
  | _, .nil => []
  | after, .slot (forked := forked) earlier _ => earlier.steps ++ [(forked, after)]
  | _, .block (fork := fork) (state := state) (after := after) earlier _ _ _ _ =>
    earlier.steps ++ [(⟨fork, state⟩, ⟨fork, after⟩)]

/-- The states of a chain, from its first state to its last, in order. -/
def states : {last : ForkedBeaconState preset} → ChainList config checks first last →
    List (ForkedBeaconState preset)
  | _, .nil => [first]
  | after, .slot earlier _ => earlier.states ++ [after]
  | _, .block (fork := fork) (after := after) earlier _ _ _ _ => earlier.states ++ [⟨fork, after⟩]

/-- The blocks that a chain applies, with the states before and after each, in order. -/
def appliedBlocks : {last : ForkedBeaconState preset} → ChainList config checks first last →
    List (AppliedBlock preset)
  | _, .nil => []
  | _, .slot earlier _ => earlier.appliedBlocks
  | _, .block (fork := fork) (state := state) (after := after) earlier _ signed _ _ =>
    earlier.appliedBlocks ++ [⟨fork, state, signed, after⟩]

/-- The messages of the blocks that a chain applies, each with its fork, in order. -/
def blocks {last : ForkedBeaconState preset} (chain : ChainList config checks first last) :
    List ((fork : Fork) × BeaconBlock preset fork) :=
  chain.appliedBlocks.map fun applied => ⟨applied.fork, applied.signed.message⟩

/-- A chain given as data is a run of steps of a chain. -/
theorem chainSteps : ∀ {last : ForkedBeaconState preset}, ChainList config checks first last →
    Relation.ReflTransGen (ChainStep config checks) first last
  | _, .nil => .refl
  | _, .slot earlier computed => earlier.chainSteps.tail (.slot computed)
  | _, .block earlier engine signed validateResult applied =>
    earlier.chainSteps.tail (.block engine signed validateResult applied)

/-- Each step of a chain is a step of a chain, reached from the first state, reaching the last. -/
theorem mem_steps : ∀ {last : ForkedBeaconState preset} (chain : ChainList config checks first last)
    {step : ForkedBeaconState preset × ForkedBeaconState preset}, step ∈ chain.steps →
    Relation.ReflTransGen (ChainStep config checks) first step.1 ∧
      ChainStep config checks step.1 step.2 ∧
      Relation.ReflTransGen (ChainStep config checks) step.2 last
  | _, .nil, _, member => absurd member List.not_mem_nil
  | _, .slot earlier computed, step, member => by
    rcases List.mem_append.mp member with older | newest
    · obtain ⟨reach, chainStep, rest⟩ := earlier.mem_steps older
      exact ⟨reach, chainStep, rest.tail (.slot computed)⟩
    · obtain rfl := List.mem_singleton.mp newest
      exact ⟨earlier.chainSteps, .slot computed, .refl⟩
  | _, .block earlier engine signed validateResult applied, step, member => by
    rcases List.mem_append.mp member with older | newest
    · obtain ⟨reach, chainStep, rest⟩ := earlier.mem_steps older
      exact ⟨reach, chainStep, rest.tail (.block engine signed validateResult applied)⟩
    · obtain rfl := List.mem_singleton.mp newest
      exact ⟨earlier.chainSteps, .block engine signed validateResult applied, .refl⟩

/-- The state after each step of a chain is one of its states. -/
theorem snd_mem_states : ∀ {last : ForkedBeaconState preset}
    (chain : ChainList config checks first last)
    {step : ForkedBeaconState preset × ForkedBeaconState preset}, step ∈ chain.steps →
    step.2 ∈ chain.states
  | _, .nil, _, member => absurd member List.not_mem_nil
  | _, .slot earlier _, _, member => by
    rcases List.mem_append.mp member with older | newest
    · exact List.mem_append_left _ (earlier.snd_mem_states older)
    · obtain rfl := List.mem_singleton.mp newest
      exact List.mem_append_right _ (List.mem_singleton_self _)
  | _, .block earlier _ _ _ _, _, member => by
    rcases List.mem_append.mp member with older | newest
    · exact List.mem_append_left _ (earlier.snd_mem_states older)
    · obtain rfl := List.mem_singleton.mp newest
      exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Each block that a chain applies is applied by a step of the chain, between its two states. -/
theorem mem_appliedBlocks : ∀ {last : ForkedBeaconState preset}
    (chain : ChainList config checks first last) {applied : AppliedBlock preset},
    applied ∈ chain.appliedBlocks →
    ((⟨applied.fork, applied.before⟩, ⟨applied.fork, applied.after⟩) :
        ForkedBeaconState preset × ForkedBeaconState preset) ∈ chain.steps ∧
      ∃ (engine : ExecutionEngine preset applied.fork) (validateResult : Bool),
        applySignedBlock config checks engine applied.before applied.signed validateResult =
          .ok applied.after
  | _, .nil, _, member => absurd member List.not_mem_nil
  | _, .slot earlier _, _, member => by
    obtain ⟨stepMember, applies⟩ := earlier.mem_appliedBlocks member
    exact ⟨List.mem_append_left _ stepMember, applies⟩
  | _, .block earlier engine _ validateResult computed, _, member => by
    rcases List.mem_append.mp member with older | newest
    · obtain ⟨stepMember, applies⟩ := earlier.mem_appliedBlocks older
      exact ⟨List.mem_append_left _ stepMember, applies⟩
    · obtain rfl := List.mem_singleton.mp newest
      exact ⟨List.mem_append_right _ (List.mem_singleton_self _), engine, validateResult, computed⟩

end ChainList

end EthLib.Consensus
